import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Varrho
import Anisotropic.Rigidity.Deform
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.MinMax

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The monotonicity and distance facts along the deformation and the end point of Lemma 10.4 -/

/-! ## Elementary facts under the density assumptions -/

private lemma dff_empMeasure_apply (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- Under the density assumptions, `N > 0` and some `σ_i` is positive. -/
private lemma dff_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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
  rw [dff_empMeasure_apply σ measurableSet_Icc] at hgap
  simp only [hall, Set.mem_Icc, le_refl, h.pos.le, and_self, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] at hgap
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hM', ENNReal.toReal_one] at hgap
  linarith [h.pos]
/-- `supp ϱ ≠ ∅` for `σ ≥ 0`, `N > 0`. -/
private lemma dff_support_nonempty (σ' : Fin M → ℝ) (hσ' : ∀ i, 0 ≤ σ' i) (hN : 0 < N) :
    (varrho N σ').support.Nonempty := by
  have := isProbabilityMeasure_varrho N σ' hσ' hN
  exact Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)

/-- `ϱ(U) = 0` for `U` avoiding `0` with density `0` on `U ∩ (0, ∞)`. -/
private lemma dff_varrho_eq_zero (N : ℕ) (σ : Fin M → ℝ) {U : Set ℝ} (hU : MeasurableSet U)
    (h0 : (0 : ℝ) ∉ U) (h : ∀ x ∈ U, 0 < x → rhoDens N σ x = 0) : varrho N σ U = 0 := by
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hU,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hU,
    Measure.restrict_restrict hU]
  refine setLIntegral_eq_zero (hU.inter measurableSet_Ioi) fun x ⟨hx1, hx2⟩ => ?_
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
  exact (h x hx1 hx2).le

/-! ## The critical points `x_1 ≥ ⋯ ≥ x_{2p−1}` and the poles between them -/

section CritPoints

open Polynomial

private lemma dff_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma dff_mem_posVals (σ : Fin M → ℝ) {i : Fin M} (hi : 0 < σ i) : σ i ∈ posVals σ := by
  simp [posVals, hi]

private lemma dff_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma dff_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (dff_mem_posVals σ hpos)

/-- For `s > 0`: `-1/s < x ↔ 0 < 1 + s x`. -/
private lemma dff_lt_iff {s x : ℝ} (hs : 0 < s) : -s⁻¹ < x ↔ 0 < 1 + s * x := by
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

private lemma dff_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma dff_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := dff_pos_of_mem σ hu
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
    (mul_ne_zero (mul_ne_zero (dff_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

/-- A point of `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)` is negative, lies in `(-s_n⁻¹, 0)`, is not a pole, and
is a critical point of `f`. -/
private lemma dff_mem_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ innerCrit N σ) :
    InInner σ x ∧ (∀ u ∈ posVals σ, 1 + u * x ≠ 0) ∧ fR1 N σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, mem_roots (dff_critPoly_ne_zero N σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly N σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := dff_pos_of_mem σ hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact dff_critPoly_pole N σ hN hu h0
  refine ⟨hin, hnp, ?_⟩
  rw [critPoly_eval N σ hσ hin.1.ne (dff_nonpole_all σ hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma dff_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
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
      have ih := dff_list_prefix y L hpw.2 j hj
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

private lemma dff_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
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
  · rw [dff_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

/-- The number of critical points in `(y, 0)`, counted with multiplicity. -/
private def dffA (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℕ :=
  Multiset.card ((innerCrit N σ).filter (fun x => y < x))

/-- `x_k ∈ 𝒞` for `1 ≤ k < 2p`, and `y < x_k` iff at least `k` critical points lie in
`(y, 0)`. -/
private lemma dff_xCrit_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ ∧ ∀ y, (y < xCrit N σ k ↔ k ≤ dffA N σ y) := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hx : xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := dff_sort_spec (innerCrit N σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y, dffA]
  omega

private lemma dff_xCrit_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k')
    (hk' : k' < 2 * numBands N σ) : xCrit N σ k' ≤ xCrit N σ k := by
  by_contra h
  rw [not_le] at h
  have h1 := ((dff_xCrit_spec N σ hσ hN hS (k := k') (by omega) hk').2 (xCrit N σ k)).1 h
  have h2 := ((dff_xCrit_spec N σ hσ hN hS hk1 (by omega)).2 (xCrit N σ k)).2 (by omega)
  exact lt_irrefl _ h2

/-- `x_k < 0` for `1 ≤ k < 2p`, and `x_k` is not a pole. -/
private lemma dff_xCrit_good (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k < 0 ∧ (∀ i, 1 + σ i * xCrit N σ k ≠ 0) ∧ fR1 N σ (xCrit N σ k) = 0 := by
  obtain ⟨hin, hnp, h1⟩ :=
    dff_mem_innerCrit N σ hσ hN (dff_xCrit_spec N σ hσ hN hS hk1 hk).1
  exact ⟨hin.1, dff_nonpole_all σ hσ hnp, h1⟩

/-- An odd number of critical points lies to the right of every pole `-1/s` (Lemma 2.4: one in
`I_1`, an even number in each other `I_l`). -/
private lemma dff_A_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (n : ℕ) :
    ∀ s ∈ posVals σ, ((posVals σ).filter (fun u => s < u)).card = n →
      Odd (dffA N σ (-s⁻¹)) := by
  have hS' : ∀ s ∈ posVals σ, (posVals σ).Nonempty := fun s hs => ⟨s, hs⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    have hs0 := dff_pos_of_mem σ hs
    by_cases hne : ((posVals σ).filter (fun u => s < u)).Nonempty
    · set s' := ((posVals σ).filter (fun u => s < u)).min' hne with hs'def
      have hm := Finset.min'_mem _ hne
      rw [← hs'def] at hm
      obtain ⟨hs'S, hss'⟩ := Finset.mem_filter.mp hm
      have hs'0 := dff_pos_of_mem σ hs'S
      have hcons : ∀ u ∈ posVals σ, ¬ (s < u ∧ u < s') := by
        rintro u hu ⟨h1, h2⟩
        have := Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, h1⟩)
        rw [← hs'def] at this
        linarith
      have hinv : -s⁻¹ < -s'⁻¹ := neg_lt_neg (inv_strictAnti₀ hs0 hss')
      have hsplit : dffA N σ (-s⁻¹) =
          Multiset.card ((innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹)) +
            dffA N σ (-s'⁻¹) := by
        unfold dffA
        have h1 := Multiset.filter_add_not (fun x : ℝ => x < -s'⁻¹)
          ((innerCrit N σ).filter (fun x => -s⁻¹ < x))
        have e1 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter (fun x => x < -s'⁻¹) =
            (innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹) := by
          rw [Multiset.filter_filter]
          exact Multiset.filter_congr fun x _ => and_comm
        have e2 : ((innerCrit N σ).filter (fun x => -s⁻¹ < x)).filter
              (fun x => ¬ x < -s'⁻¹) = (innerCrit N σ).filter (fun x => -s'⁻¹ < x) := by
          rw [Multiset.filter_filter]
          refine Multiset.filter_congr fun x hx => ?_
          have hnp := (dff_mem_innerCrit N σ hσ hN hx).2.1 s' hs'S
          have hne' : x ≠ -s'⁻¹ := by
            intro h
            apply hnp
            rw [h]
            field_simp
            ring
          constructor
          · rintro ⟨h1, -⟩
            exact lt_of_le_of_ne (not_lt.mp h1) hne'.symm
          · intro h
            exact ⟨not_lt.mpr h.le, lt_trans hinv h⟩
        rw [← h1, Multiset.card_add, e1, e2]
      have hsub : (posVals σ).filter (fun u => s' < u) ⊆ (posVals σ).filter (fun u => s < u) := by
        intro u hu
        obtain ⟨huT, hu'⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨huT, lt_trans hss' hu'⟩
      have hlt : ((posVals σ).filter (fun u => s' < u)).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
          ⟨s', Finset.mem_filter.mpr ⟨hs'S, hss'⟩, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩)
      have ho := ih _ hlt s' hs'S rfl
      rw [hsplit]
      rcases card_innerCrit_Ii N σ hσ hN hs hs'S hss' hcons with h | h
      · rw [h, zero_add]
        exact ho
      · rw [h]
        rw [add_comm]
        exact ho.add_even even_two
    · have hmax : ∀ u ∈ posVals σ, u ≤ s := by
        intro u hu
        by_contra h
        exact hne ⟨u, Finset.mem_filter.mpr ⟨hu, lt_of_not_ge h⟩⟩
      have e : (innerCrit N σ).filter (fun x => -s⁻¹ < x) =
          (innerCrit N σ).filter (fun x => ∀ u ∈ posVals σ, 0 < 1 + u * x) := by
        refine Multiset.filter_congr fun x hx => ?_
        have hx0 := (dff_mem_innerCrit N σ hσ hN hx).1.1
        rw [dff_lt_iff hs0]
        constructor
        · intro h u hu
          have := mul_le_mul_of_nonpos_right (hmax u hu) hx0.le
          linarith
        · intro h
          exact h s hs
      unfold dffA
      rw [e, card_innerCrit_I1 N σ hσ hN (hS' s hs)]
      exact odd_one

/-- Exactly one critical point lies to the right of the largest pole (Lemma 2.4). -/
private lemma dff_A_max (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) : dffA N σ (-((posVals σ).max' hS)⁻¹) = 1 := by
  set s := (posVals σ).max' hS with hsdef
  have hs : s ∈ posVals σ := (posVals σ).max'_mem hS
  have hs0 := dff_pos_of_mem σ hs
  have hmax : ∀ u ∈ posVals σ, u ≤ s := fun u hu => (posVals σ).le_max' u hu
  have e : (innerCrit N σ).filter (fun x => -s⁻¹ < x) =
      (innerCrit N σ).filter (fun x => ∀ u ∈ posVals σ, 0 < 1 + u * x) := by
    refine Multiset.filter_congr fun x hx => ?_
    have hx0 := (dff_mem_innerCrit N σ hσ hN hx).1.1
    rw [dff_lt_iff hs0]
    constructor
    · intro h u hu
      have := mul_le_mul_of_nonpos_right (hmax u hu) hx0.le
      linarith
    · intro h
      exact h s hs
  unfold dffA
  rw [e, card_innerCrit_I1 N σ hσ hN hS]

end CritPoints

/-! ## The gap `(x_{2k+1}, x_{2k})` and the constant `C_x` -/

/-- The `k`-th gap, `1 ≤ k < p`: `x_{2k+1} ≤ x_{2k} < 0` are critical points with values
`a_{2k+1} ≥ 0` and `a_{2k}`; every pole lies in `(x_{2k}, 0)` (the top block) or to the left of
`x_{2k+1}`; the top block is nonempty. -/
private lemma dff_gap {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k < numBands N σ) :
    xCrit N σ (2 * k + 1) ≤ xCrit N σ (2 * k) ∧ xCrit N σ (2 * k) < 0 ∧
      fR1 N σ (xCrit N σ (2 * k)) = 0 ∧ fR1 N σ (xCrit N σ (2 * k + 1)) = 0 ∧
      fR N σ (xCrit N σ (2 * k)) = edgeVal N σ (2 * k) ∧
      fR N σ (xCrit N σ (2 * k + 1)) = edgeVal N σ (2 * k + 1) ∧
      0 ≤ edgeVal N σ (2 * k + 1) ∧
      (∀ i, ¬ 1 + σ i * xCrit N σ (2 * k) < 0 → 0 < 1 + σ i * xCrit N σ (2 * k + 1)) ∧
      (∃ i, 1 + σ i * xCrit N σ (2 * k) < 0) := by
  obtain ⟨hN, hS⟩ := dff_facts h
  have hσ := h.nonneg
  have hp := card_innerCrit N σ hσ hN hS
  have hk2 : 2 * k < 2 * numBands N σ := by omega
  have hk3 : 2 * k + 1 < 2 * numBands N σ := by omega
  obtain ⟨hx0, hxnp, hx1⟩ := dff_xCrit_good N σ hσ hN hS (k := 2 * k) (by omega) hk2
  obtain ⟨-, -, hy1⟩ := dff_xCrit_good N σ hσ hN hS (k := 2 * k + 1) (by omega) hk3
  have hyx := dff_xCrit_anti N σ hσ hN hS (k := 2 * k) (k' := 2 * k + 1) (by omega) (by omega)
    hk3
  have hspec := fun {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 2 * numBands N σ) =>
    (dff_xCrit_spec N σ hσ hN hS hm1 hm).2
  refine ⟨hyx, hx0, hx1, hy1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold edgeVal
    rw [ite_eq_right (by omega)]
  · unfold edgeVal
    rw [ite_eq_right (by omega)]
  · exact (edgeVal_mem_Icc N σ hσ hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma
      (k := 2 * k + 1) (by omega) (by omega)).1
  · intro i hi
    rcases (hσ i).eq_or_lt with h0 | h0
    · rw [← h0]; norm_num
    · have hlt : -(σ i)⁻¹ < xCrit N σ (2 * k) :=
        (dff_lt_iff h0).2 (lt_of_le_of_ne (not_lt.mp hi) (Ne.symm (hxnp i)))
      have hA := (hspec (m := 2 * k) (by omega) hk2 _).1 hlt
      obtain ⟨c, hc⟩ := dff_A_odd N σ hσ hN _ (σ i) (dff_mem_posVals σ h0) rfl
      exact (dff_lt_iff h0).1 ((hspec (m := 2 * k + 1) (by omega) hk3 _).2 (by omega))
  · by_contra hno
    push Not at hno
    have hs := (posVals σ).max'_mem hS
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    have h0 : 0 < σ i := hi ▸ dff_pos_of_mem σ hs
    have hlt : -(σ i)⁻¹ < xCrit N σ (2 * k) :=
      (dff_lt_iff h0).2 (lt_of_le_of_ne (hno i) (Ne.symm (hxnp i)))
    have hA := (hspec (m := 2 * k) (by omega) hk2 _).1 hlt
    rw [hi, dff_A_max N σ hσ hN hS] at hA
    omega

/-- Some `σ_i` is positive. -/
private lemma dff_exists_pos {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    ∃ i, 0 < σ i := by
  obtain ⟨-, s, hs⟩ := dff_facts h
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  exact ⟨i, hi ▸ dff_pos_of_mem σ hs⟩

private lemma dff_tau_le_one {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) : τ ≤ 1 := by
  have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
  by_contra hc
  have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_of_not_ge hc)
  linarith

/-- `C_x ≥ 4` for `0 < τ ≤ 1`. -/
private lemma dff_C_ge {τ τg : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτg : 0 < τg) :
    4 ≤ gapCx τ τg := by
  have hκ : 1 ≤ kappaMax τ := by
    have : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
    unfold kappaMax
    nlinarith
  unfold gapCx mBoundConst genPropConst
  set τx := min (τg / 2) (kappaMax τ)⁻¹ with hτx
  have h1 : 0 < τx := lt_min (by linarith) (inv_pos.mpr (by linarith))
  have h2 : τx ≤ 1 := (min_le_right _ _).trans (inv_le_one_of_one_le₀ hκ)
  have h3 : 0 < τx / 2 := by positivity
  have h4 : (τx / 2) ^ 4 ≤ 1 := pow_le_one₀ h3.le (by linarith)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Real points lie in the closure of `ℂ₊`. -/
private lemma dff_neBot (E : ℝ) : (𝓝[upperHalf] (E : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
  simp

/-- Lemma 4.10 at a real point `E` of `(τ', τ'⁻¹)`, as the limit from `ℂ₊`:
`|m(E + i0)| ≥ C(τ')⁻¹`. -/
private lemma dff_norm_mExt_ge {τ' : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ' N σ) {E : ℝ}
    (hE : τ' < E) (hE' : E < τ'⁻¹) : (genPropConst τ')⁻¹ ≤ ‖mExt N σ E‖ := by
  have hE0 : 0 < E := lt_trans h.pos hE
  have := dff_neBot E
  have ht := (tendsto_mFun_of_ne_zero N σ h.nonneg hE0.ne').norm
  have hopen : IsOpen {z : ℂ | τ' < ‖z‖ ∧ ‖z‖ < τ'⁻¹} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hmem : (E : ℂ) ∈ {z : ℂ | τ' < ‖z‖ ∧ ‖z‖ < τ'⁻¹} := by
    simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0]
    exact ⟨hE, hE'⟩
  have hev : ∀ᶠ z in 𝓝[upperHalf] (E : ℂ), (genPropConst τ')⁻¹ ≤ ‖mFun N σ z‖ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem),
      self_mem_nhdsWithin] with z hz hz'
    exact (gen_prop_m h hz' hz.1.le hz.2.le).1
  exact ge_of_tendsto ht hev

/-- `|x_{2k}| ≥ C_x⁻¹` (Lemma 4.10 at the real point `a_{2k}`). -/
private lemma dff_x_ge {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (ha : τg ≤ edgeVal N σ (2 * k)) : (gapCx τ τg)⁻¹ ≤ -xCrit N σ (2 * k) := by
  obtain ⟨hN, hS⟩ := dff_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  set τx := min (τg / 2) (kappaMax τ)⁻¹ with hτx
  set τ' := τx / 2 with hτ'
  have hκ : τ⁻¹ ≤ kappaMax τ := by unfold kappaMax; nlinarith
  have hκpos : 0 < kappaMax τ := lt_of_lt_of_le hτi hκ
  have hτxpos : 0 < τx := lt_min (by linarith) (inv_pos.mpr hκpos)
  have hτ'pos : 0 < τ' := by positivity
  have hτ'x : τ' < τx := by linarith
  have hτ'τ : τ' ≤ τ :=
    hτ'x.le.trans ((min_le_right _ _).trans (inv_le_of_inv_le₀ hτ hκ))
  have hC : gapCx τ τg = genPropConst τ' := rfl
  have hk2 : 2 * k < 2 * numBands N σ := by omega
  obtain ⟨hx0, -, -⟩ := dff_xCrit_good N σ hσ hN hS (k := 2 * k) (by omega) hk2
  have hma : mExt N σ (edgeVal N σ (2 * k)) = xCrit N σ (2 * k) :=
    mExt_edgeVal N σ hσ hN hS (k := 2 * k) (by omega) hk2.le (fun h => by omega)
  have ha_le : edgeVal N σ (2 * k) ≤ 2 * τ⁻¹ * (1 + τ⁻¹) :=
    (edgeVal_mem_Icc N σ hσ hN hS hτ h.phi_lower h.phi_upper h.bound_Sigma (k := 2 * k)
      (by omega) hk2.le).2
  have hlow : τ' < edgeVal N σ (2 * k) := by
    have : τx ≤ τg / 2 := min_le_left _ _
    linarith
  have hup : edgeVal N σ (2 * k) < τ'⁻¹ := by
    have h1 : kappaMax τ ≤ τx⁻¹ := by
      have := inv_anti₀ hτxpos (min_le_right (τg / 2) (kappaMax τ)⁻¹)
      rwa [inv_inv] at this
    have h2 : τx⁻¹ < τ'⁻¹ := inv_strictAnti₀ hτ'pos hτ'x
    have h3 : 2 * τ⁻¹ * (1 + τ⁻¹) < kappaMax τ := by unfold kappaMax; linarith
    linarith
  have := dff_norm_mExt_ge (h.mono hτ'pos hτ'τ) hlow hup
  rw [hma, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx0] at this
  rw [hC]
  exact this

/-! ## `f` on a pole-free segment -/

/-- On a pole-free segment `[lo, hi]` every `1 + σ_i x` keeps its sign. -/
private lemma dff_pf_sign {σ' : Fin M → ℝ} (hσ' : ∀ i, 0 ≤ σ' i) {lo hi : ℝ}
    (hpf : ∀ i, 1 + σ' i * hi < 0 ∨ 0 < 1 + σ' i * lo) {x : ℝ} (hx : x ∈ Set.Icc lo hi)
    (i : Fin M) : 1 + σ' i * x < 0 ∨ 0 < 1 + σ' i * x := by
  rcases hpf i with h | h
  · left
    have := mul_le_mul_of_nonneg_left hx.2 (hσ' i)
    linarith
  · right
    have := mul_le_mul_of_nonneg_left hx.1 (hσ' i)
    linarith

private lemma dff_pf_ne {σ' : Fin M → ℝ} (hσ' : ∀ i, 0 ≤ σ' i) {lo hi : ℝ}
    (hpf : ∀ i, 1 + σ' i * hi < 0 ∨ 0 < 1 + σ' i * lo) {x : ℝ} (hx : x ∈ Set.Icc lo hi)
    (i : Fin M) : 1 + σ' i * x ≠ 0 := by
  rcases dff_pf_sign hσ' hpf hx i with h | h
  · exact h.ne
  · exact h.ne'

/-- `f` is continuous off `0` and the poles. -/
private lemma dff_fR_cont (N : ℕ) (σ' : Fin M → ℝ) (hN : 0 < N) {S : Set ℝ}
    (h0 : ∀ x ∈ S, x ≠ 0) (hnp : ∀ x ∈ S, ∀ i, 1 + σ' i * x ≠ 0) :
    ContinuousOn (fR N σ') S := by
  have hfun : fR N σ' = fun x => -x⁻¹ + ∑ i, σ' i / (N * (1 + σ' i * x)) := by
    funext x; rfl
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hfun]
  refine ((continuousOn_inv₀.mono fun x hx => Set.mem_compl_singleton_iff.mpr (h0 x hx)).neg).add
    ?_
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine continuousOn_const.div (by fun_prop) fun x hx => ?_
  exact mul_ne_zero hN'.ne' (hnp x hx i)

/-- Strict convexity of `v ↦ v⁻²` on each half-line. -/
private lemma dff_inv_sq_lt {v₁ v₂ a b : ℝ} (hv : 0 < v₁ * v₂) (hne : v₁ ≠ v₂) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) :
    1 / (a * v₁ + b * v₂) ^ 2 < a * (1 / v₁ ^ 2) + b * (1 / v₂ ^ 2) := by
  have hc := (strictConvexOn_zpow (m := -2) (by norm_num) (by norm_num)).2
  have key : ∀ w₁ w₂ : ℝ, 0 < w₁ → 0 < w₂ → w₁ ≠ w₂ →
      1 / (a * w₁ + b * w₂) ^ 2 < a * (1 / w₁ ^ 2) + b * (1 / w₂ ^ 2) := by
    intro w₁ w₂ h₁ h₂ hw
    have := hc (Set.mem_Ioi.mpr h₁) (Set.mem_Ioi.mpr h₂) hw ha hb hab
    simpa [smul_eq_mul, _root_.zpow_neg, one_div] using this
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact key v₁ v₂ h₁ h₂ hne
  · have := key (-v₁) (-v₂) (by linarith) (by linarith) (fun h => hne (by linarith))
    have e1 : (a * -v₁ + b * -v₂) ^ 2 = (a * v₁ + b * v₂) ^ 2 := by ring
    have e2 : (-v₁) ^ 2 = v₁ ^ 2 := by ring
    have e3 : (-v₂) ^ 2 = v₂ ^ 2 := by ring
    rwa [e1, e2, e3] at this

/-- `x² f'(x) = 1 − Σ_i (σ_i²/N) (x⁻¹ + σ_i)⁻²` off `0` and the poles. -/
private lemma dff_fR1_chart (N : ℕ) (σ' : Fin M → ℝ) (hN : 0 < N) {x : ℝ} (hx : x ≠ 0)
    (hnp : ∀ i, 1 + σ' i * x ≠ 0) :
    x ^ 2 * fR1 N σ' x = 1 - ∑ i, σ' i ^ 2 / N * (1 / (x⁻¹ + σ' i) ^ 2) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold fR1
  rw [mul_sub, mul_inv_cancel₀ (pow_ne_zero 2 hx), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : x⁻¹ + σ' i = (1 + σ' i * x) / x := by field_simp
  have := hnp i
  rw [e]
  field_simp

/-- Concavity of `x² f'(x)` in `1/x` on a pole-free segment (with a positive `σ_i`): if
`f' ≥ 0` at both ends of `[x₁, x₂] ⊂ (−∞, 0)`, then `f' > 0` inside. -/
private lemma dff_conc (N : ℕ) (σ' : Fin M → ℝ) (hσ' : ∀ i, 0 ≤ σ' i) (hN : 0 < N)
    (hS : ∃ i, 0 < σ' i) {x₁ x₂ x : ℝ} (h₁ : x₁ < x) (h₂ : x < x₂) (h₀ : x₂ < 0)
    (hpf : ∀ i, 1 + σ' i * x₂ < 0 ∨ 0 < 1 + σ' i * x₁)
    (hd₁ : 0 ≤ fR1 N σ' x₁) (hd₂ : 0 ≤ fR1 N σ' x₂) : 0 < fR1 N σ' x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : x < 0 := h₂.trans h₀
  have hx10 : x₁ < 0 := h₁.trans hx0
  have hm1 : x₁ ∈ Set.Icc x₁ x₂ := ⟨le_rfl, (h₁.trans h₂).le⟩
  have hm2 : x₂ ∈ Set.Icc x₁ x₂ := ⟨(h₁.trans h₂).le, le_rfl⟩
  have hm : x ∈ Set.Icc x₁ x₂ := ⟨h₁.le, h₂.le⟩
  have c1 := dff_fR1_chart N σ' hN hx10.ne fun i => dff_pf_ne hσ' hpf hm1 i
  have c2 := dff_fR1_chart N σ' hN h₀.ne fun i => dff_pf_ne hσ' hpf hm2 i
  have c := dff_fR1_chart N σ' hN hx0.ne fun i => dff_pf_ne hσ' hpf hm i
  set u₁ := x₁⁻¹ with hu₁
  set u₂ := x₂⁻¹ with hu₂
  set u := x⁻¹ with hu
  have h21 : u₂ < u := (inv_lt_inv_of_neg h₀ hx0).2 h₂
  have h22 : u < u₁ := (inv_lt_inv_of_neg hx0 hx10).2 h₁
  set a := (u - u₂) / (u₁ - u₂) with hadef
  set b := (u₁ - u) / (u₁ - u₂) with hbdef
  have hd : 0 < u₁ - u₂ := by linarith
  have ha : 0 < a := div_pos (by linarith) hd
  have hb : 0 < b := div_pos (by linarith) hd
  have hab : a + b = 1 := by rw [hadef, hbdef, ← add_div]; field_simp; ring
  have hcomb : ∀ s : ℝ, u + s = a * (u₁ + s) + b * (u₂ + s) := by
    intro s
    rw [hadef, hbdef]
    field_simp
    ring
  have hx1ne : x₁ ≠ 0 := hx10.ne
  have hx2ne : x₂ ≠ 0 := h₀.ne
  have hside : ∀ i, 0 < (u₁ + σ' i) * (u₂ + σ' i) := by
    intro i
    have hmono := mul_le_mul_of_nonneg_left (h₁.trans h₂).le (hσ' i)
    have e : (u₁ + σ' i) * (u₂ + σ' i) =
        ((1 + σ' i * x₁) * (1 + σ' i * x₂)) / (x₁ * x₂) := by
      rw [hu₁, hu₂]; field_simp
    rw [e]
    refine div_pos ?_ (mul_pos_of_neg_of_neg hx10 h₀)
    rcases dff_pf_sign hσ' hpf hm1 i with h1 | h1 <;>
      rcases dff_pf_sign hσ' hpf hm2 i with h2 | h2
    · exact mul_pos_of_neg_of_neg h1 h2
    · rcases hpf i with h | h <;> linarith
    · linarith
    · exact mul_pos h1 h2
  have hterm : ∀ i, 1 / (u + σ' i) ^ 2 <
      a * (1 / (u₁ + σ' i) ^ 2) + b * (1 / (u₂ + σ' i) ^ 2) := by
    intro i
    rw [hcomb (σ' i)]
    exact dff_inv_sq_lt (hside i) (fun h => by linarith) ha hb hab
  have hsum : ∑ i, σ' i ^ 2 / N * (1 / (u + σ' i) ^ 2) <
      a * ∑ i, σ' i ^ 2 / N * (1 / (u₁ + σ' i) ^ 2) +
        b * ∑ i, σ' i ^ 2 / N * (1 / (u₂ + σ' i) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    obtain ⟨i₀, hi₀⟩ := hS
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
    · have hc0 : 0 ≤ σ' i ^ 2 / N := by positivity
      have := mul_le_mul_of_nonneg_left (hterm i).le hc0
      linarith
    · have hc0 : 0 < σ' i₀ ^ 2 / N := by positivity
      have := mul_lt_mul_of_pos_left (hterm i₀) hc0
      linarith
  have hpos : 0 < x ^ 2 * fR1 N σ' x := by
    rw [c]
    have e1 : 0 ≤ x₁ ^ 2 * fR1 N σ' x₁ := mul_nonneg (sq_nonneg _) hd₁
    have e2 : 0 ≤ x₂ ^ 2 * fR1 N σ' x₂ := mul_nonneg (sq_nonneg _) hd₂
    rw [c1] at e1
    rw [c2] at e2
    nlinarith
  by_contra hc
  have : x ^ 2 * fR1 N σ' x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_lt.mp hc)
  linarith

/-- On a pole-free segment `[lo, hi] ⊂ (−∞, 0)` with `f' > 0` inside and `f(lo) ≥ 0`, the
interval `(f(lo), f(hi))` misses `supp ϱ`. -/
private lemma dff_gap_support (N : ℕ) (σ' : Fin M → ℝ) (hσ' : ∀ i, 0 ≤ σ' i) (hN : 0 < N)
    {lo hi : ℝ} (hlh : lo < hi) (hhi : hi < 0)
    (hpf : ∀ i, 1 + σ' i * hi < 0 ∨ 0 < 1 + σ' i * lo)
    (hd : ∀ x ∈ Set.Ioo lo hi, 0 < fR1 N σ' x) (h0 : 0 ≤ fR N σ' lo) :
    ∀ s ∈ (varrho N σ').support, s ≤ fR N σ' lo ∨ fR N σ' hi ≤ s := by
  intro s hs
  by_contra hcon
  push Not at hcon
  have hcont := dff_fR_cont N σ' hN (S := Set.Icc lo hi)
    (fun x hx => (lt_of_le_of_lt hx.2 hhi).ne) (fun x hx i => dff_pf_ne hσ' hpf hx i)
  have hzero : varrho N σ' (Set.Ioo (fR N σ' lo) (fR N σ' hi)) = 0 := by
    refine dff_varrho_eq_zero N σ' measurableSet_Ioo (fun hm => by linarith [hm.1])
      fun E hE hE0 => ?_
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hlh.le hcont hE
    unfold rhoDens
    rw [← hfx, mExt_fR_of_pos N σ' hσ' hN (hx.2.trans hhi).ne
      (fun i => dff_pf_ne hσ' hpf ⟨hx.1.le, hx.2.le⟩ i) (by rw [hfx]; exact hE0.ne') (hd x hx),
      Complex.ofReal_im, zero_div]
  exact (Measure.notMem_support_iff_exists.2 ⟨_, Ioo_mem_nhds hcon.1 hcon.2, hzero⟩) hs

/-- `f(x₂) − f(x₁) ≤ (x₂ − x₁)/(x₁ x₂)` on a pole-free segment `[x₁, x₂] ⊂ (−∞, 0)`. -/
private lemma dff_fR_sub_le (N : ℕ) (σ' : Fin M → ℝ) (hσ' : ∀ i, 0 ≤ σ' i) (hN : 0 < N)
    {x₁ x₂ : ℝ} (h₁₂ : x₁ < x₂) (h₀ : x₂ < 0)
    (hpf : ∀ i, 1 + σ' i * x₂ < 0 ∨ 0 < 1 + σ' i * x₁) :
    fR N σ' x₂ - fR N σ' x₁ ≤ (x₂ - x₁) / (x₁ * x₂) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx10 : x₁ < 0 := h₁₂.trans h₀
  have hm1 : x₁ ∈ Set.Icc x₁ x₂ := ⟨le_rfl, h₁₂.le⟩
  have hm2 : x₂ ∈ Set.Icc x₁ x₂ := ⟨h₁₂.le, le_rfl⟩
  have hterm : ∀ i, σ' i / (N * (1 + σ' i * x₂)) - σ' i / (N * (1 + σ' i * x₁)) ≤ 0 := by
    intro i
    have hD : 0 < (1 + σ' i * x₁) * (1 + σ' i * x₂) := by
      rcases hpf i with h | h
      · have := mul_le_mul_of_nonneg_left h₁₂.le (hσ' i)
        exact mul_pos_of_neg_of_neg (by linarith) h
      · have := mul_le_mul_of_nonneg_left h₁₂.le (hσ' i)
        exact mul_pos h (by linarith)
    have hn1 := dff_pf_ne hσ' hpf hm1 i
    have hn2 := dff_pf_ne hσ' hpf hm2 i
    rw [div_sub_div _ _ (mul_ne_zero hN'.ne' hn2) (mul_ne_zero hN'.ne' hn1)]
    apply div_nonpos_of_nonpos_of_nonneg
    · have e : σ' i * (N * (1 + σ' i * x₁)) - N * (1 + σ' i * x₂) * σ' i =
          N * σ' i ^ 2 * (x₁ - x₂) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    · have e : N * (1 + σ' i * x₂) * (N * (1 + σ' i * x₁)) =
          N ^ 2 * ((1 + σ' i * x₁) * (1 + σ' i * x₂)) := by ring
      rw [e]
      positivity
  have hs := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib] at hs
  have hx1ne : x₁ ≠ 0 := hx10.ne
  have hx2ne : x₂ ≠ 0 := h₀.ne
  have e : -x₂⁻¹ - -x₁⁻¹ = (x₂ - x₁) / (x₁ * x₂) := by
    field_simp
    ring
  unfold fR
  linarith

/-! ## The deformation `σ(t)` near the gap -/

private lemma dff_sig_one (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : deformSig N σ k 1 = σ := by
  funext i
  unfold deformSig
  split_ifs <;> simp

private lemma dff_sig_nonneg {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, 0 ≤ deformSig N σ k t i := by
  intro i
  unfold deformSig
  split_ifs
  · exact mul_nonneg ht (hσ i)
  · exact hσ i

/-- On the top block, `σ_i > 0` and `1 + tσ_i z ≤ 1 + σ_i z ≤ 1 + σ_i x` for `t ≥ 1`,
`z ≤ x`, `z < 0`. -/
private lemma dff_top {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {x : ℝ} {i : Fin M}
    (hi : 1 + σ i * x < 0) {t z : ℝ} (ht : 1 ≤ t) (hz0 : z < 0) (hz : z ≤ x) :
    0 < σ i ∧ 1 + t * σ i * z ≤ 1 + σ i * z ∧ 1 + σ i * z ≤ 1 + σ i * x := by
  have hσi : 0 < σ i := by
    rcases (hσ i).eq_or_lt with h0 | h0
    · rw [← h0] at hi; norm_num at hi
    · exact h0
  have h1 : σ i * z ≤ σ i * x := mul_le_mul_of_nonneg_left hz hσi.le
  have h2 : σ i * z < 0 := mul_neg_of_pos_of_neg hσi hz0
  have h3 : t * (σ i * z) ≤ 1 * (σ i * z) := mul_le_mul_of_nonpos_right ht h2.le
  refine ⟨hσi, ?_, by linarith⟩
  rw [mul_assoc]
  linarith

/-- `f_t(z) − f_s(z) = (t − s) Σ_{top} σ_i / (N (1 + tσ_i z)(1 + sσ_i z))` for `z ≤ x_{2k}`. -/
private lemma dff_E_sub (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (k : ℕ)
    {t s z : ℝ} (ht : 1 ≤ t) (hs : 1 ≤ s) (hz0 : z < 0) (hz : z ≤ xCrit N σ (2 * k)) :
    fR N (deformSig N σ k t) z - fR N (deformSig N σ k s) z =
      (t - s) * ∑ i, (if 1 + σ i * xCrit N σ (2 * k) < 0 then
        σ i / (N * ((1 + t * σ i * z) * (1 + s * σ i * z))) else 0) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ i, deformSig N σ k t i / (N * (1 + deformSig N σ k t i * z)) -
      deformSig N σ k s i / (N * (1 + deformSig N σ k s i * z)) =
      (t - s) * (if 1 + σ i * xCrit N σ (2 * k) < 0 then
        σ i / (N * ((1 + t * σ i * z) * (1 + s * σ i * z))) else 0) := by
    intro i
    unfold deformSig
    split_ifs with hi
    · obtain ⟨-, ht1, h1⟩ := dff_top hσ hi ht hz0 hz
      obtain ⟨-, hs1, -⟩ := dff_top hσ hi hs hz0 hz
      have hDt : 1 + t * σ i * z ≠ 0 := by linarith
      have hDs : 1 + s * σ i * z ≠ 0 := by linarith
      have hNA : (N : ℝ) * (1 + t * σ i * z) ≠ 0 := mul_ne_zero hN'.ne' hDt
      have hNB : (N : ℝ) * (1 + s * σ i * z) ≠ 0 := mul_ne_zero hN'.ne' hDs
      rw [div_sub_div _ _ hNA hNB, mul_div_assoc', div_eq_div_iff (mul_ne_zero hNA hNB)
        (mul_ne_zero hN'.ne' (mul_ne_zero hDt hDs))]
      ring
    · simp
  unfold fR
  rw [Finset.mul_sum, ← Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib]
  ring

private lemma dff_term_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (k : ℕ)
    {t s z : ℝ} (ht : 1 ≤ t) (hs : 1 ≤ s) (hz0 : z < 0) (hz : z ≤ xCrit N σ (2 * k))
    (i : Fin M) :
    0 ≤ (if 1 + σ i * xCrit N σ (2 * k) < 0 then
      σ i / (N * ((1 + t * σ i * z) * (1 + s * σ i * z))) else 0) := by
  split_ifs with hi
  · obtain ⟨hσi, ht1, h1⟩ := dff_top hσ hi ht hz0 hz
    obtain ⟨-, hs1, -⟩ := dff_top hσ hi hs hz0 hz
    exact div_nonneg hσi.le (mul_nonneg (Nat.cast_nonneg _)
      (mul_pos_of_neg_of_neg (by linarith) (by linarith)).le)
  · exact le_rfl

/-- `f_t − f` is nondecreasing on `(−∞, x_{2k}]`. -/
private lemma dff_diff_mono (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (k : ℕ)
    {t z₁ z₂ : ℝ} (ht : 1 ≤ t) (hz : z₁ ≤ z₂) (hz₂ : z₂ ≤ xCrit N σ (2 * k)) (hz0 : z₂ < 0) :
    fR N (deformSig N σ k t) z₁ - fR N σ z₁ ≤ fR N (deformSig N σ k t) z₂ - fR N σ z₂ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := dff_E_sub N σ hσ hN k (s := 1) ht le_rfl (hz.trans_lt hz0) (hz.trans hz₂)
  have h2 := dff_E_sub N σ hσ hN k (s := 1) ht le_rfl hz0 hz₂
  rw [dff_sig_one] at h1 h2
  rw [h1, h2]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by linarith)
  split_ifs with hi
  · obtain ⟨hσi, a1, b1⟩ := dff_top hσ hi ht (hz.trans_lt hz0) (hz.trans hz₂)
    obtain ⟨-, a2, b2⟩ := dff_top hσ hi ht hz0 hz₂
    have m1 : t * σ i * z₁ ≤ t * σ i * z₂ :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    have m2 : 1 * σ i * z₁ ≤ 1 * σ i * z₂ := mul_le_mul_of_nonneg_left hz (by positivity)
    have hP2 : 0 < (1 + t * σ i * z₂) * (1 + 1 * σ i * z₂) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hP : (1 + t * σ i * z₂) * (1 + 1 * σ i * z₂) ≤
        (1 + t * σ i * z₁) * (1 + 1 * σ i * z₁) := by
      nlinarith
    exact div_le_div_of_nonneg_left hσi.le (mul_pos hN' hP2) (mul_le_mul_of_nonneg_left hP hN'.le)
  · exact le_rfl

/-- `f'(z) ≤ f_t'(z)` for `z ≤ x_{2k}`, `z < 0`, `t ≥ 1`. -/
private lemma dff_fR1_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (k : ℕ)
    {t z : ℝ} (ht : 1 ≤ t) (hz0 : z < 0) (hz : z ≤ xCrit N σ (2 * k)) :
    fR1 N σ z ≤ fR1 N (deformSig N σ k t) z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∑ i, deformSig N σ k t i ^ 2 / (N * (1 + deformSig N σ k t i * z) ^ 2) ≤
      ∑ i, σ i ^ 2 / (N * (1 + σ i * z) ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    unfold deformSig
    split_ifs with hi
    · obtain ⟨hσi, a1, b1⟩ := dff_top hσ hi ht hz0 hz
      have h3 : t * (-(1 + σ i * z)) ≤ -(1 + t * σ i * z) := by
        have : t * σ i * z = t * (σ i * z) := by ring
        nlinarith
      have h4 : 0 ≤ t * (-(1 + σ i * z)) := mul_nonneg (by linarith) (by linarith)
      have h5 := mul_self_le_mul_self h4 h3
      have hD1 : 0 < (1 + σ i * z) ^ 2 := by nlinarith
      have hDt : 0 < (1 + t * σ i * z) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : (t * σ i) ^ 2 * (N * (1 + σ i * z) ^ 2) =
          (σ i ^ 2 * N) * ((t * (-(1 + σ i * z))) * (t * (-(1 + σ i * z)))) := by ring
      have e2 : σ i ^ 2 * (N * (1 + t * σ i * z) ^ 2) =
          (σ i ^ 2 * N) * ((-(1 + t * σ i * z)) * (-(1 + t * σ i * z))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    · exact le_rfl
  unfold fR1
  linarith

/-- `x_mid ∈ (x_{2k+1}, x_{2k})` and `f(x_mid) = θ_k`. -/
private lemma dff_xMid {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hτg : 0 < τg)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) :
    xCrit N σ (2 * k + 1) < xMid N σ k ∧ xMid N σ k < xCrit N σ (2 * k) ∧
      fR N σ (xMid N σ k) = gapMid N σ k := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  obtain ⟨hyx, hx0, hx1, hy1, hfx, hfy, hb0, hpf, -⟩ := dff_gap h hk hkp
  have hyx' : xCrit N σ (2 * k + 1) < xCrit N σ (2 * k) := by
    rcases hyx.eq_or_lt with he | hlt
    · exfalso
      rw [he] at hfy
      linarith
    · exact hlt
  have hpf' : ∀ i, 1 + σ i * xCrit N σ (2 * k) < 0 ∨ 0 < 1 + σ i * xCrit N σ (2 * k + 1) :=
    fun i => by
      by_cases hi : 1 + σ i * xCrit N σ (2 * k) < 0
      · exact Or.inl hi
      · exact Or.inr (hpf i hi)
  have hcont := dff_fR_cont N σ hN (S := Set.Icc (xCrit N σ (2 * k + 1)) (xCrit N σ (2 * k)))
    (fun z hz => (lt_of_le_of_lt hz.2 hx0).ne) (fun z hz i => dff_pf_ne hσ hpf' hz i)
  have hθ : gapMid N σ k ∈
      Set.Ioo (fR N σ (xCrit N σ (2 * k + 1))) (fR N σ (xCrit N σ (2 * k))) := by
    rw [hfx, hfy]
    unfold gapMid
    constructor <;> linarith
  obtain ⟨xs, hxs, hfxs⟩ := intermediate_value_Ioo hyx'.le hcont hθ
  have hd : 0 < fR1 N σ xs :=
    dff_conc N σ hσ hN (dff_exists_pos h) hxs.1 hxs.2 hx0 hpf' hy1.ge hx1.ge
  have hθpos : 0 < gapMid N σ k := by unfold gapMid; linarith
  have hm := mExt_fR_of_pos N σ hσ hN (hxs.2.trans hx0).ne
    (fun i => dff_pf_ne hσ hpf' ⟨hxs.1.le, hxs.2.le⟩ i) (by rw [hfxs]; exact hθpos.ne') hd
  have hxm : xMid N σ k = xs := by
    unfold xMid
    rw [← hfxs, hm, Complex.ofReal_re]
  rw [hxm]
  exact ⟨hxs.1, hxs.2, hfxs⟩

/-! ## Lemma 10.4: the moving window and the end point -/

/-- `x_{2k} − x_mid ≥ τ_g/(2C_x²)` and `x_mid − x_{2k+1} ≥ τ_g/(2C_x²)`. -/
private lemma dff_mid_bounds {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) :
    τg / (2 * gapCx τ τg ^ 2) ≤ xCrit N σ (2 * k) - xMid N σ k ∧
      τg / (2 * gapCx τ τg ^ 2) ≤ xMid N σ k - xCrit N σ (2 * k + 1) := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  obtain ⟨hyx, hx0, -, -, hfx, hfy, -, hpf, -⟩ := dff_gap h hk hkp
  obtain ⟨hym, hmx, hfm⟩ := dff_xMid h hτg hk hkp hg
  have hC4 := dff_C_ge h.pos (dff_tau_le_one h) hτg
  have hCx := dff_x_ge h hτg hk hkp ha
  set x := xCrit N σ (2 * k) with hxdef
  set y := xCrit N σ (2 * k + 1) with hydef
  set xm := xMid N σ k with hxmdef
  set C := gapCx τ τg with hCdef
  have hCpos : 0 < C := by linarith
  have hθ : gapMid N σ k = (edgeVal N σ (2 * k) + edgeVal N σ (2 * k + 1)) / 2 := rfl
  have hpf1 : ∀ i, 1 + σ i * x < 0 ∨ 0 < 1 + σ i * xm := fun i => by
    by_cases hi : 1 + σ i * x < 0
    · exact Or.inl hi
    · have := mul_le_mul_of_nonneg_left hym.le (hσ i)
      exact Or.inr (by linarith [hpf i hi])
  have hpf2 : ∀ i, 1 + σ i * xm < 0 ∨ 0 < 1 + σ i * y := fun i => by
    by_cases hi : 1 + σ i * x < 0
    · have := mul_le_mul_of_nonneg_left hmx.le (hσ i)
      exact Or.inl (by linarith)
    · exact Or.inr (hpf i hi)
  have i1 := dff_fR_sub_le N σ hσ hN hmx hx0 hpf1
  have i2 := dff_fR_sub_le N σ hσ hN hym (hmx.trans hx0) hpf2
  have hCi : 0 < C⁻¹ := inv_pos.mpr hCpos
  have hCC : C⁻¹ ^ 2 * C ^ 2 = 1 := by field_simp
  -- `1/(z₁ z₂) ≤ C²` for `z₁ ≤ z₂ ≤ x < 0`
  have key : ∀ z₁ z₂ : ℝ, z₁ < z₂ → z₂ ≤ x → (z₂ - z₁) / (z₁ * z₂) ≤ (z₂ - z₁) * C ^ 2 := by
    intro z₁ z₂ h12 h2x
    have hp : C⁻¹ ^ 2 ≤ z₁ * z₂ := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    have : (z₂ - z₁) * 1 ≤ (z₂ - z₁) * (C ^ 2 * (z₁ * z₂)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    linarith
  have k1 := key xm x hmx le_rfl
  have k2 := key y xm hym hmx.le
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- `|B| ≤ N` for the top block `B`. -/
private lemma dff_card_le {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (ha : τg ≤ edgeVal N σ (2 * k)) :
    ((Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0).card : ℝ) ≤
      (1 - τ / gapCx τ τg) * N := by
  rw [topBlock_card h hk hkp]
  exact (topBlock_bounds h hτg hk hkp ha).1

/-- The window of Lemma 10.4 at time `t ≥ 1`: `f_t' > 0` on `(x_{2k+1}, x_{2k})`, and
`E_t − f_t(x_{2k+1}) ≥ (a_{2k} − a_{2k+1})/2`, `f_t(x_{2k}) − E_t ≥ (a_{2k} − a_{2k+1})/2`,
`f_t(x_{2k+1}) ≥ 0`. -/
private lemma dff_window {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ fR N (deformSig N σ k t) (xCrit N σ (2 * k + 1)) ∧
      τg / 2 ≤ deformE N σ k t - fR N (deformSig N σ k t) (xCrit N σ (2 * k + 1)) ∧
      τg / 2 ≤ fR N (deformSig N σ k t) (xCrit N σ (2 * k)) - deformE N σ k t ∧
      0 ≤ fR1 N (deformSig N σ k t) (xCrit N σ (2 * k + 1)) := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  obtain ⟨hyx, hx0, -, hy1, hfx, hfy, hb0, -, -⟩ := dff_gap h hk hkp
  obtain ⟨hym, hmx, hfm⟩ := dff_xMid h hτg hk hkp hg
  have hθ : gapMid N σ k = (edgeVal N σ (2 * k) + edgeVal N σ (2 * k + 1)) / 2 := rfl
  have hy0 : xCrit N σ (2 * k + 1) < 0 := hyx.trans_lt hx0
  have hbt : fR N σ (xCrit N σ (2 * k + 1)) ≤
      fR N (deformSig N σ k t) (xCrit N σ (2 * k + 1)) := by
    have he := dff_E_sub N σ hσ hN k (t := t) (s := 1) ht le_rfl hy0 hyx
    rw [dff_sig_one] at he
    have hs := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      dff_term_nonneg N σ hσ k (t := t) (s := 1) ht le_rfl hy0 hyx i
    nlinarith
  have hm1 := dff_diff_mono N σ hσ hN k ht hym.le hmx.le (hmx.trans hx0)
  have hm2 := dff_diff_mono N σ hσ hN k ht hmx.le le_rfl hx0
  have hE : deformE N σ k t = fR N (deformSig N σ k t) (xMid N σ k) := rfl
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  exact hy1.ge.trans (dff_fR1_le N σ hσ hN k ht hy0 hyx)

/-- The window `[E_t ± τ_g/4]` stays at distance `≥ τ_g/4` from `supp ϱ_t`. -/
private lemma dff_window_dist {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) {t : ℝ} (ht : 1 ≤ t) :
    ∀ E ∈ Set.Icc (deformE N σ k t - τg / 4) (deformE N σ k t + τg / 4),
      τg / 4 ≤ Metric.infDist E (varrho N (deformSig N σ k t)).support := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  obtain ⟨hyx, hx0, hx1, hy1, -, -, -, hpf, -⟩ := dff_gap h hk hkp
  obtain ⟨hym, hmx, -⟩ := dff_xMid h hτg hk hkp hg
  have hy0 : xCrit N σ (2 * k + 1) < 0 := hyx.trans_lt hx0
  intro E hE
  have hσt : ∀ i, 0 ≤ deformSig N σ k t i := dff_sig_nonneg hσ k (by linarith)
  have hpft : ∀ i, 1 + deformSig N σ k t i * xCrit N σ (2 * k) < 0 ∨
      0 < 1 + deformSig N σ k t i * xCrit N σ (2 * k + 1) := by
    intro i
    unfold deformSig
    split_ifs with hi
    · obtain ⟨-, a1, -⟩ := dff_top hσ hi ht hx0 le_rfl
      exact Or.inl (by linarith)
    · exact Or.inr (hpf i hi)
  have hSt : ∃ i, 0 < deformSig N σ k t i := by
    obtain ⟨i, hi⟩ := dff_exists_pos h
    refine ⟨i, ?_⟩
    unfold deformSig
    split_ifs
    · exact mul_pos (by linarith) hi
    · exact hi
  have hdt : ∀ z ∈ Set.Ioo (xCrit N σ (2 * k + 1)) (xCrit N σ (2 * k)),
      0 < fR1 N (deformSig N σ k t) z := fun z hz =>
    dff_conc N _ hσt hN hSt hz.1 hz.2 hx0 hpft
      (hy1.ge.trans (dff_fR1_le N σ hσ hN k ht hy0 hyx))
      (hx1.ge.trans (dff_fR1_le N σ hσ hN k ht hx0 le_rfl))
  obtain ⟨hbt, hw1, hw2, -⟩ := dff_window h hτg hk hkp hg ht
  have hW := dff_gap_support N _ hσt hN (hym.trans hmx) hx0 hpft hdt hbt
  rw [Metric.le_infDist (dff_support_nonempty _ hσt hN)]
  intro s hs
  rw [Real.dist_eq]
  rcases hW s hs with h1 | h1
  · rw [abs_of_nonneg (by linarith [hE.1])]
    linarith [hE.1]
  · rw [abs_of_nonpos (by linarith [hE.2])]
    linarith [hE.2]

/-- `|E_t − E_s| ≤ L |t − s|` with `L = 4C_x⁵/τ_g²`. -/
private lemma dff_lip {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hτg : 0 < τg)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ) (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) {t s : ℝ} (ht : 1 ≤ t)
    (hs : 1 ≤ s) : |deformE N σ k t - deformE N σ k s| ≤ deformL τ τg * |t - s| := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨-, hx0, -⟩ := dff_gap h hk hkp
  obtain ⟨-, hmx, -⟩ := dff_xMid h hτg hk hkp hg
  obtain ⟨hδ, -⟩ := dff_mid_bounds h hτg hk hkp ha hg
  have hC4 := dff_C_ge hτ (dff_tau_le_one h) hτg
  have hcard := dff_card_le h hτg hk hkp ha
  have htop := (topBlock_bounds h hτg hk hkp ha).2
  set x := xCrit N σ (2 * k) with hxdef
  set xm := xMid N σ k with hxmdef
  set C := gapCx τ τg with hCdef
  have hCpos : 0 < C := by linarith
  have hτC : 0 ≤ τ / C := by positivity
  have he := dff_E_sub N σ hσ hN k ht hs (hmx.trans hx0) hmx.le
  unfold deformE
  rw [he, abs_mul, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
    dff_term_nonneg N σ hσ k ht hs (hmx.trans hx0) hmx.le i)]
  set δ := x - xm with hδdef
  have hδpos : 0 < δ := by linarith
  have hterm : ∀ i, (if 1 + σ i * x < 0 then
      σ i / (N * ((1 + t * σ i * xm) * (1 + s * σ i * xm))) else 0) ≤
      (if 1 + σ i * x < 0 then C / (N * δ ^ 2) else 0) := by
    intro i
    split_ifs with hi
    · obtain ⟨hσi, a1, b1⟩ := dff_top hσ hi ht (hmx.trans hx0) hmx.le
      obtain ⟨-, a2, -⟩ := dff_top hσ hi hs (hmx.trans hx0) hmx.le
      have hσC : 1 ≤ C * σ i := by
        have := htop i hi
        rw [inv_le_iff_one_le_mul₀' hCpos] at this
        exact this
      have hD : σ i * δ ≤ -(1 + σ i * xm) := by
        have e : σ i * δ = σ i * x - σ i * xm := by rw [hδdef]; ring
        linarith
      have hσδ : 0 ≤ σ i * δ := by positivity
      have hP : (σ i * δ) * (σ i * δ) ≤
          (-(1 + t * σ i * xm)) * (-(1 + s * σ i * xm)) :=
        mul_le_mul (by linarith) (by linarith) hσδ (by linarith)
      have hPpos : 0 < (1 + t * σ i * xm) * (1 + s * σ i * xm) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      rw [div_le_div_iff₀ (mul_pos hN' hPpos) (by positivity)]
      have e : (-(1 + t * σ i * xm)) * (-(1 + s * σ i * xm)) =
          (1 + t * σ i * xm) * (1 + s * σ i * xm) := by ring
      rw [e] at hP
      calc σ i * (N * δ ^ 2) = σ i * (N * δ ^ 2) * 1 := (mul_one _).symm
        _ ≤ σ i * (N * δ ^ 2) * (C * σ i) := mul_le_mul_of_nonneg_left hσC (by positivity)
        _ = C * (N * (σ i * δ * (σ i * δ))) := by ring
        _ ≤ C * (N * ((1 + t * σ i * xm) * (1 + s * σ i * xm))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hN'.le) hCpos.le
    · exact le_rfl
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  have hR : ∑ i, (if 1 + σ i * x < 0 then C / (N * δ ^ 2) else 0) =
      ((Finset.univ.filter fun i => 1 + σ i * x < 0).card : ℝ) * (C / (N * δ ^ 2)) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hR] at hsum
  have hcardN : ((Finset.univ.filter fun i => 1 + σ i * x < 0).card : ℝ) ≤ N := by
    have : (1 - τ / C) * N ≤ N := by nlinarith
    linarith
  have hB : ((Finset.univ.filter fun i => 1 + σ i * x < 0).card : ℝ) * (C / (N * δ ^ 2)) ≤
      C / δ ^ 2 := by
    have e : ((Finset.univ.filter fun i => 1 + σ i * x < 0).card : ℝ) * (C / (N * δ ^ 2)) =
        (((Finset.univ.filter fun i => 1 + σ i * x < 0).card : ℝ) / N) * (C / δ ^ 2) := by
      rw [div_mul_div_comm, mul_div_assoc']
    rw [e]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one hN').2 hcardN)
  have hL : C / δ ^ 2 ≤ deformL τ τg := by
    unfold deformL
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : τg ≤ 2 * C ^ 2 * δ := by
      rw [div_le_iff₀ (by positivity)] at hδ
      linarith
    have h2 : τg ^ 2 ≤ (2 * C ^ 2 * δ) ^ 2 := pow_le_pow_left₀ hτg.le h1 2
    calc C * τg ^ 2 ≤ C * (2 * C ^ 2 * δ) ^ 2 := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = 4 * C ^ 5 * δ ^ 2 := by ring
  calc |t - s| * _ ≤ |t - s| * (C / δ ^ 2) :=
        mul_le_mul_of_nonneg_left (hsum.trans hB) (abs_nonneg _)
    _ ≤ |t - s| * deformL τ τg := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
    _ = deformL τ τg * |t - s| := mul_comm _ _

/-- `E_t ≤ C_x + 2τ⁻¹C_x²/τ_g`. -/
private lemma dff_emax {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hτg : 0 < τg)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ) (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) {t : ℝ} (ht : 1 ≤ t) :
    deformE N σ k t ≤ deformEmax τ τg := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hyx, hx0, -, -, -, -, -, hpf, -⟩ := dff_gap h hk hkp
  obtain ⟨hym, hmx, -⟩ := dff_xMid h hτg hk hkp hg
  obtain ⟨-, hδ'⟩ := dff_mid_bounds h hτg hk hkp ha hg
  have hC4 := dff_C_ge hτ (dff_tau_le_one h) hτg
  have hCx := dff_x_ge h hτg hk hkp ha
  set x := xCrit N σ (2 * k) with hxdef
  set y := xCrit N σ (2 * k + 1) with hydef
  set xm := xMid N σ k with hxmdef
  set C := gapCx τ τg with hCdef
  have hCpos : 0 < C := by linarith
  have hxm0 : xm < 0 := hmx.trans hx0
  have h1 : -xm⁻¹ ≤ C := by
    rw [neg_inv]
    have hpos : 0 < -xm := by linarith
    exact (inv_le_comm₀ hpos hCpos).2 (by linarith)
  have hd : 0 < xm - y := by linarith
  have hterm : ∀ i, deformSig N σ k t i / (N * (1 + deformSig N σ k t i * xm)) ≤
      1 / (N * (xm - y)) := by
    intro i
    unfold deformSig
    split_ifs with hi
    · obtain ⟨hσi, a1, b1⟩ := dff_top hσ hi ht hxm0 hmx.le
      have : t * σ i / (N * (1 + t * σ i * xm)) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonneg_of_nonpos hN'.le (by linarith))
      exact this.trans (by positivity)
    · have hy := hpf i hi
      have hm := mul_le_mul_of_nonneg_left hym.le (hσ i)
      have hpos : 0 < 1 + σ i * xm := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e : σ i * (N * (xm - y)) = N * (σ i * xm - σ i * y) := by ring
      rw [e]
      have : σ i * xm - σ i * y ≤ 1 + σ i * xm := by linarith
      calc N * (σ i * xm - σ i * y) ≤ N * (1 + σ i * xm) :=
            mul_le_mul_of_nonneg_left this hN'.le
        _ = 1 * (N * (1 + σ i * xm)) := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hphi : (M : ℝ) / N ≤ τ⁻¹ := h.phi_upper
  have h2 : (M : ℝ) * (1 / (N * (xm - y))) ≤ τ⁻¹ * (2 * C ^ 2 / τg) := by
    have e : (M : ℝ) * (1 / (N * (xm - y))) = (M / N) * (1 / (xm - y)) := by
      field_simp
    rw [e]
    refine mul_le_mul hphi ?_ (by positivity) (by positivity)
    rw [div_le_div_iff₀ hd hτg]
    rw [div_le_iff₀ (by positivity)] at hδ'
    linarith
  unfold deformE fR deformEmax
  have e : 2 * τ⁻¹ * C ^ 2 / τg = τ⁻¹ * (2 * C ^ 2 / τg) := by ring
  rw [← hCdef, e]
  linarith

/-- Four facts along the deformation of Lemma 10.4: `E_1 = θ_k`, the moving window
stays at distance `≥ τ_g/4` from `supp ϱ_t`, `t ↦ E_t` is Lipschitz, and `E_t` is bounded. -/
theorem deform_facts {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hτg : 0 < τg)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ) (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) :
    deformE N σ k 1 = gapMid N σ k ∧
      (∀ t, 1 ≤ t → ∀ E ∈ Set.Icc (deformE N σ k t - τg / 4) (deformE N σ k t + τg / 4),
        τg / 4 ≤ Metric.infDist E (varrho N (deformSig N σ k t)).support) ∧
      (∀ t s, 1 ≤ t → 1 ≤ s → |deformE N σ k t - deformE N σ k s| ≤ deformL τ τg * |t - s|) ∧
      (∀ t, 1 ≤ t → deformE N σ k t ≤ deformEmax τ τg) := by
  refine ⟨?_, fun t ht => dff_window_dist h hτg hk hkp hg ht,
    fun t s ht hs => dff_lip h hτg hk hkp ha hg ht hs, fun t ht => dff_emax h hτg hk hkp ha hg ht⟩
  unfold deformE
  rw [dff_sig_one]
  exact (dff_xMid h hτg hk hkp hg).2.2

/-- Monotonicity of the moving threshold (Lemma 10.4): `θ_k = E_1 ≤ E_t` for `t ≥ 1`. -/
theorem deformE_ge_gapMid {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) {t : ℝ} (ht : 1 ≤ t) :
    gapMid N σ k ≤ deformE N σ k t := by
  obtain ⟨hN, -⟩ := dff_facts h
  obtain ⟨-, hx0, -⟩ := dff_gap h hk hkp
  obtain ⟨-, hmx, hfm⟩ := dff_xMid h hτg hk hkp hg
  have he := dff_E_sub N σ h.nonneg hN k (t := t) (s := 1) ht le_rfl (hmx.trans hx0) hmx.le
  rw [dff_sig_one, hfm] at he
  have hs := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    dff_term_nonneg N σ h.nonneg k (t := t) (s := 1) ht le_rfl (hmx.trans hx0) hmx.le i
  unfold deformE
  nlinarith

/-- `f_T(−z) ≥ z⁻¹ − c W` and `f_T'(−z) ≥ z⁻² − c W² − 4τ⁻³` at a point `−z` to the right of
`x_{2k}`, where on the top block `Tσ_i ≤ W |1 − Tσ_i z|`, and `c N` bounds the top block. -/
private lemma dff_end_bounds {τ c W T z : ℝ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hτ : 0 < τ) (hT : 0 ≤ T) (hb : ∀ i, σ i ≤ τ⁻¹) (hphi : (M : ℝ) / N ≤ τ⁻¹) (k : ℕ) (hW : 0 ≤ W)
    (hz0 : 0 < z) (hzτ : z ≤ τ / 2)
    (hB : ∀ i, 1 + σ i * xCrit N σ (2 * k) < 0 →
      0 < -(1 + T * σ i * -z) ∧ T * σ i ≤ W * (-(1 + T * σ i * -z)))
    (hcard : ((Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0).card : ℝ) ≤ c * N) :
    z⁻¹ - c * W ≤ fR N (deformSig N σ k T) (-z) ∧
      (z ^ 2)⁻¹ - c * W ^ 2 - 4 * τ⁻¹ ^ 3 ≤ fR1 N (deformSig N σ k T) (-z) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set B := Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0 with hBdef
  have hrest : ∀ i, 1 / 2 ≤ 1 + σ i * -z := by
    intro i
    have h1 : σ i * z ≤ τ⁻¹ * (τ / 2) :=
      mul_le_mul (hb i) hzτ hz0.le (inv_nonneg.mpr hτ.le)
    have h2 : τ⁻¹ * (τ / 2) = 1 / 2 := by field_simp
    linarith
  have hcN : (B.card : ℝ) / N ≤ c := by rw [div_le_iff₀ hN']; exact hcard
  constructor
  · have hterm : ∀ i, (if 1 + σ i * xCrit N σ (2 * k) < 0 then -(W / N) else 0) ≤
        deformSig N σ k T i / (N * (1 + deformSig N σ k T i * -z)) := by
      intro i
      unfold deformSig
      split_ifs with hi
      · obtain ⟨hD, hle⟩ := hB i hi
        have h1 : T * σ i / (N * (-(1 + T * σ i * -z))) ≤ W / N := by
          rw [div_le_div_iff₀ (by positivity) hN']
          calc T * σ i * N ≤ W * (-(1 + T * σ i * -z)) * N :=
                mul_le_mul_of_nonneg_right hle hN'.le
            _ = W * (N * (-(1 + T * σ i * -z))) := by ring
        have h2 : T * σ i / (N * (1 + T * σ i * -z)) =
            -(T * σ i / (N * (-(1 + T * σ i * -z)))) := by
          rw [← div_neg]
          congr 1
          ring
        linarith
      · have := hrest i
        exact div_nonneg (hσ i) (by positivity)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      ← hBdef] at hsum
    have h3 : (B.card : ℝ) * (W / N) ≤ c * W := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc, mul_comm c W]
      exact mul_le_mul_of_nonneg_left hcN hW
    unfold fR
    rw [inv_neg, neg_neg]
    linarith
  · have hterm : ∀ i, deformSig N σ k T i ^ 2 / (N * (1 + deformSig N σ k T i * -z) ^ 2) ≤
        (if 1 + σ i * xCrit N σ (2 * k) < 0 then W ^ 2 / N else 0) + 4 * τ⁻¹ ^ 2 / N := by
      intro i
      unfold deformSig
      split_ifs with hi
      · obtain ⟨hD, hle⟩ := hB i hi
        have h1 : (T * σ i) ^ 2 / (N * (1 + T * σ i * -z) ^ 2) ≤ W ^ 2 / N := by
          have hsq : 0 < (1 + T * σ i * -z) ^ 2 := by nlinarith
          rw [div_le_div_iff₀ (mul_pos hN' hsq) hN']
          have hTσ : 0 ≤ T * σ i := mul_nonneg hT (hσ i)
          have h2 : (T * σ i) ^ 2 ≤ (W * (-(1 + T * σ i * -z))) ^ 2 :=
            pow_le_pow_left₀ hTσ hle 2
          calc (T * σ i) ^ 2 * N ≤ (W * (-(1 + T * σ i * -z))) ^ 2 * N :=
                mul_le_mul_of_nonneg_right h2 hN'.le
            _ = W ^ 2 * (N * (1 + T * σ i * -z) ^ 2) := by ring
        have h3 : 0 ≤ 4 * τ⁻¹ ^ 2 / N := by positivity
        linarith
      · have h1 := hrest i
        have h2 : σ i ^ 2 ≤ τ⁻¹ ^ 2 := pow_le_pow_left₀ (hσ i) (hb i) 2
        have h3 : 1 / 4 ≤ (1 + σ i * -z) ^ 2 := by nlinarith
        rw [zero_add, div_le_div_iff₀ (by positivity) hN']
        calc σ i ^ 2 * N ≤ τ⁻¹ ^ 2 * N := mul_le_mul_of_nonneg_right h2 hN'.le
          _ = 4 * τ⁻¹ ^ 2 * (N * (1 / 4)) := by ring
          _ ≤ 4 * τ⁻¹ ^ 2 * (N * (1 + σ i * -z) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hN'.le) (by positivity)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      nsmul_eq_mul, ← hBdef] at hsum
    have h3 : (B.card : ℝ) * (W ^ 2 / N) ≤ c * W ^ 2 := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc, mul_comm c (W ^ 2)]
      exact mul_le_mul_of_nonneg_left hcN (sq_nonneg W)
    have h4 : (M : ℝ) * (4 * τ⁻¹ ^ 2 / N) ≤ 4 * τ⁻¹ ^ 3 := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc]
      calc 4 * τ⁻¹ ^ 2 * (M / N) ≤ 4 * τ⁻¹ ^ 2 * τ⁻¹ :=
            mul_le_mul_of_nonneg_left hphi (by have := inv_pos.mpr hτ; positivity)
        _ = 4 * τ⁻¹ ^ 3 := by ring
    unfold fR1
    rw [neg_sq]
    linarith

/-- The value bound at the end point: `|R| + τ_g ≤ z⁻¹ − (1 − τ/C) W` for
`z = 2C²/(τT)`, `W = τT/(C(2C − τ))`. -/
private lemma dff_alg_f {τ τg C T R : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 4 ≤ C) (hT0 : 0 < T)
    (hT5 : 4 * C ^ 3 * (|R| + τg) / τ ^ 2 ≤ T) :
    |R| + τg ≤ (2 * C ^ 2 / (τ * T))⁻¹ - (1 - τ / C) * (τ * T / (C * (2 * C - τ))) := by
  have hCpos : 0 < C := by linarith
  have h2C : 0 < 2 * C - τ := by linarith
  have hid : (2 * C ^ 2 / (τ * T))⁻¹ - (1 - τ / C) * (τ * T / (C * (2 * C - τ))) =
      τ ^ 2 * T / (2 * C ^ 2 * (2 * C - τ)) := by
    field_simp
    ring
  have hle : 2 * C ^ 2 * (2 * C - τ) ≤ 4 * C ^ 3 := by
    have : 2 * C ^ 2 * τ ≥ 0 := by positivity
    nlinarith
  have hge : τ ^ 2 * T / (4 * C ^ 3) ≤ τ ^ 2 * T / (2 * C ^ 2 * (2 * C - τ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hle
  have h5 : |R| + τg ≤ τ ^ 2 * T / (4 * C ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hT5
    linarith
  rw [hid]
  linarith

/-- The derivative bound at the end point: `z⁻² − (1 − τ/C) W² − 4τ⁻³ > 0`. -/
private lemma dff_alg_d {τ C T : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 4 ≤ C) (hT0 : 0 < T)
    (hT4 : 9 * C ^ 3 / τ ^ 4 ≤ T) :
    0 < ((2 * C ^ 2 / (τ * T)) ^ 2)⁻¹ - (1 - τ / C) * (τ * T / (C * (2 * C - τ))) ^ 2 -
      4 * τ⁻¹ ^ 3 := by
  have hCpos : 0 < C := by linarith
  have h2C : 0 < 2 * C - τ := by linarith
  have hid : ((2 * C ^ 2 / (τ * T)) ^ 2)⁻¹ - (1 - τ / C) * (τ * T / (C * (2 * C - τ))) ^ 2 =
      τ ^ 4 * T ^ 2 / (4 * C ^ 4 * (2 * C - τ) ^ 2) := by
    field_simp
    ring
  have hge : τ ^ 4 * T ^ 2 / (16 * C ^ 6) ≤ τ ^ 4 * T ^ 2 / (4 * C ^ 4 * (2 * C - τ) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have h1 : (2 * C - τ) ^ 2 ≤ (2 * C) ^ 2 := pow_le_pow_left₀ h2C.le (by linarith) 2
    calc 4 * C ^ 4 * (2 * C - τ) ^ 2 ≤ 4 * C ^ 4 * (2 * C) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 * C ^ 6 := by ring
  have hT4' : 9 * C ^ 3 ≤ T * τ ^ 4 := by
    rw [div_le_iff₀ (by positivity)] at hT4
    exact hT4
  have hsq : 81 * C ^ 6 ≤ T ^ 2 * τ ^ 8 := by
    have h1 := pow_le_pow_left₀ (by positivity) hT4' 2
    calc 81 * C ^ 6 = (9 * C ^ 3) ^ 2 := by ring
      _ ≤ (T * τ ^ 4) ^ 2 := h1
      _ = T ^ 2 * τ ^ 8 := by ring
  have hτ8 : T ^ 2 * τ ^ 8 ≤ T ^ 2 * τ ^ 7 := by
    have : τ ^ 8 ≤ τ ^ 7 := pow_le_pow_of_le_one hτ.le hτ1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hlt : 4 * τ⁻¹ ^ 3 < τ ^ 4 * T ^ 2 / (16 * C ^ 6) := by
    rw [inv_pow, ← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hC6 : 0 < C ^ 6 := by positivity
    have e : τ ^ 4 * T ^ 2 * τ ^ 3 = T ^ 2 * τ ^ 7 := by ring
    rw [e]
    linarith
  rw [hid]
  linarith

/-- The end point of Lemma 10.4 for one `T` satisfying the lower bounds of `T₀`. -/
private lemma dff_end_core {τ τg R T : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) (hT1 : 1 ≤ T)
    (hT2 : 4 * gapCx τ τg ^ 3 / τ ≤ T) (hT3 : 4 * gapCx τ τg ^ 2 / τ ^ 2 ≤ T)
    (hT4 : 9 * gapCx τ τg ^ 3 / τ ^ 4 ≤ T)
    (hT5 : 4 * gapCx τ τg ^ 3 * (|R| + τg) / τ ^ 2 ≤ T) :
    ∀ E ∈ Set.Icc (deformE N σ k T) R,
      τg / 4 ≤ Metric.infDist E (varrho N (deformSig N σ k T)).support := by
  obtain ⟨hN, -⟩ := dff_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have hτ1 := dff_tau_le_one h
  obtain ⟨hyx, hx0, -, -, -, -, -, hpf, -⟩ := dff_gap h hk hkp
  have hC4 := dff_C_ge hτ hτ1 hτg
  have hCx := dff_x_ge h hτg hk hkp ha
  have hcard := dff_card_le h hτg hk hkp ha
  have htop := (topBlock_bounds h hτg hk hkp ha).2
  obtain ⟨hbt, hw1, -, hdy⟩ := dff_window h hτg hk hkp hg hT1
  set x := xCrit N σ (2 * k) with hxdef
  set y := xCrit N σ (2 * k + 1) with hydef
  set C := gapCx τ τg with hCdef
  have hCpos : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  -- the point `−z`, `z = 2C²/(τT)`
  set z := 2 * C ^ 2 / (τ * T) with hzdef
  have hz0 : 0 < z := by positivity
  have hzC : z ≤ 1 / (2 * C) := by
    rw [hzdef, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ hτ] at hT2
    nlinarith
  have hzτ : z ≤ τ / 2 := by
    rw [hzdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    rw [div_le_iff₀ (by positivity)] at hT3
    nlinarith
  have hxK : x < -z := by
    have : 1 / (2 * C) < C⁻¹ := by
      rw [one_div]
      exact inv_strictAnti₀ hCpos (by linarith)
    linarith
  have hxK0 : -z < 0 := by linarith
  set W := τ * T / (C * (2 * C - τ)) with hWdef
  have h2C : 0 < 2 * C - τ := by linarith
  have hW0 : 0 < W := by positivity
  have hBterm : ∀ i, 1 + σ i * x < 0 →
      0 < -(1 + T * σ i * -z) ∧ T * σ i ≤ W * (-(1 + T * σ i * -z)) := by
    intro i hi
    have hσi : 0 < σ i := (dff_top hσ hi le_rfl hx0 le_rfl).1
    have hσC : 1 ≤ C * σ i := by
      have := htop i hi
      rwa [inv_le_iff_one_le_mul₀' hCpos] at this
    have e2 : -(1 + T * σ i * -z) = 2 * C ^ 2 * σ i / τ - 1 := by
      rw [hzdef]
      field_simp
      ring
    rw [e2]
    have hq : 2 * C ≤ 2 * C ^ 2 * σ i / τ := by
      rw [le_div_iff₀ hτ]
      nlinarith
    refine ⟨by linarith, ?_⟩
    rw [hWdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e3 : τ * T * (2 * C ^ 2 * σ i / τ - 1) = 2 * C ^ 2 * σ i * T - τ * T := by
      field_simp
    rw [e3]
    have := mul_le_mul_of_nonneg_left hσC (by positivity : 0 ≤ τ * T)
    nlinarith
  obtain ⟨hfK, hdK⟩ := dff_end_bounds hσ hN hτ hT0.le h.bound_Sigma h.phi_upper k hW0.le hz0
    hzτ hBterm hcard
  have hfK' : |R| + τg ≤ fR N (deformSig N σ k T) (-z) :=
    (dff_alg_f hτ hτ1 hC4 hT0 hT5).trans hfK
  have hdK' : 0 < fR1 N (deformSig N σ k T) (-z) :=
    lt_of_lt_of_le (dff_alg_d hτ hτ1 hC4 hT0 hT4) hdK
  -- `f_T' > 0` on `(x_{2k+1}, −z)`, and the gap
  have hσT : ∀ i, 0 ≤ deformSig N σ k T i := dff_sig_nonneg hσ k hT0.le
  have hpfT : ∀ i, 1 + deformSig N σ k T i * -z < 0 ∨ 0 < 1 + deformSig N σ k T i * y := by
    intro i
    unfold deformSig
    split_ifs with hi
    · left
      linarith [(hBterm i hi).1]
    · exact Or.inr (hpf i hi)
  have hST : ∃ i, 0 < deformSig N σ k T i := by
    obtain ⟨i, hi⟩ := dff_exists_pos h
    refine ⟨i, ?_⟩
    unfold deformSig
    split_ifs
    · exact mul_pos hT0 hi
    · exact hi
  have hyK : y < -z := hyx.trans_lt hxK
  have hdT : ∀ w ∈ Set.Ioo y (-z), 0 < fR1 N (deformSig N σ k T) w := fun w hw =>
    dff_conc N _ hσT hN hST hw.1 hw.2 hxK0 hpfT hdy hdK'.le
  have hW := dff_gap_support N _ hσT hN hyK hxK0 hpfT hdT hbt
  intro E hE
  rw [Metric.le_infDist (dff_support_nonempty _ hσT hN)]
  intro s hs
  rw [Real.dist_eq]
  have hR : R ≤ |R| := le_abs_self R
  rcases hW s hs with h1 | h1
  · rw [abs_of_nonneg (by linarith [hE.1])]
    linarith [hE.1]
  · rw [abs_of_nonpos (by linarith [hE.2])]
    linarith [hE.2]

/-- For `T ≥ T₀(τ, τ_g, R)`, the whole interval `[E_T, R]` lies in a gap of `ϱ_T` at distance
`≥ τ_g/4` from `supp ϱ_T`. -/
theorem deform_end (τ τg R : ℝ) (hτ : 0 < τ) (hτg : 0 < τg) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T ≥ T₀, ∀ {N M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
      DensityAssumptions τ N σ → 1 ≤ k → k < numBands N σ → τg ≤ edgeVal N σ (2 * k) →
      τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1) →
      ∀ E ∈ Set.Icc (deformE N σ k T) R,
        τg / 4 ≤ Metric.infDist E (varrho N (deformSig N σ k T)).support := by
  refine ⟨max 1 (max (4 * gapCx τ τg ^ 3 / τ) (max (4 * gapCx τ τg ^ 2 / τ ^ 2)
    (max (9 * gapCx τ τg ^ 3 / τ ^ 4) (4 * gapCx τ τg ^ 3 * (|R| + τg) / τ ^ 2)))),
    le_max_left _ _, ?_⟩
  intro T hT N M σ k h hk hkp ha hg
  simp only [ge_iff_le, max_le_iff] at hT
  obtain ⟨hT1, hT2, hT3, hT4, hT5⟩ := hT
  exact dff_end_core h hτg hk hkp ha hg hT1 hT2 hT3 hT4 hT5

/-! ## The matrices `Q(t) = Xᵀ Σ(t) X` -/

/-- `‖Xᵀ diag(v) X‖ ≤ ‖v‖_∞ ‖XᵀX‖`. -/
private lemma dff_norm_XDX (Xm : Matrix (Fin M) (Fin N) ℝ) (v : Fin M → ℝ) :
    ‖Xmᵀ * diagonal v * Xm‖ ≤ ‖v‖ * ‖Xmᵀ * Xm‖ := by
  have h1 : ‖Xmᵀ * diagonal v * Xm‖ ≤ ‖Xmᵀ‖ * ‖diagonal v‖ * ‖Xm‖ :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
  have h2 : ‖Xmᵀ‖ = ‖Xm‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  have h3 : ‖Xmᵀ * Xm‖ = ‖Xm‖ * ‖Xm‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose_mul_self]
  rw [Matrix.l2_opNorm_diagonal, h2] at h1
  rw [h3]
  calc _ ≤ ‖Xm‖ * ‖v‖ * ‖Xm‖ := h1
    _ = ‖v‖ * (‖Xm‖ * ‖Xm‖) := by ring

private lemma dff_dot_self_nonneg {K : ℕ} (v : Fin K → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `Xᵀ diag(v) X` is symmetric. -/
private lemma dff_herm (Xm : Matrix (Fin M) (Fin N) ℝ) (v : Fin M → ℝ) :
    (Xmᵀ * diagonal v * Xm).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- The end point `t = T` of Lemma 10.4, deterministic: if the top-block rows of `X` satisfy
`c' |u|² ≤ |Xᵀu|²`, `σ ≥ s` on the top block, `σ ≤ τ⁻¹` and `‖XᵀX‖ ≤ C₀`, then
`n(E) = d_k` for `τ⁻¹ C₀ < E ≤ T s c'`. -/
theorem eigCount_deform_end {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) {τ C₀ c' s T E : ℝ} (k : ℕ)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (hc' : 0 < c') (hs : 0 < s) (hT : 1 ≤ T)
    (hlow : ∀ u : Fin M → ℝ, (∀ i, ¬ (1 + σ i * xCrit N σ (2 * k) < 0) → u i = 0) →
      c' * (u ⬝ᵥ u) ≤ Xmᵀ *ᵥ u ⬝ᵥ Xmᵀ *ᵥ u)
    (htop : ∀ i, 1 + σ i * xCrit N σ (2 * k) < 0 → s ≤ σ i) (hτ : 0 < τ)
    (hσle : ∀ i, σ i ≤ τ⁻¹) (hnorm : ‖Xmᵀ * Xm‖ ≤ C₀) (hE₁ : τ⁻¹ * C₀ < E)
    (hE₂ : E ≤ T * s * c') :
    eigCount (QN (diagonal (deformSig N σ k T)) Xm) E =
      (Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0).card := by
  set P : Fin M → Prop := fun i => 1 + σ i * xCrit N σ (2 * k) < 0 with hPdef
  set vR : Fin M → ℝ := fun i => if P i then 0 else σ i with hvR
  set vB : Fin M → ℝ := fun i => if P i then T * σ i else 0 with hvB
  have hT0 : 0 < T := by linarith
  have hQ : QN (diagonal (deformSig N σ k T)) Xm =
      Xmᵀ * diagonal vR * Xm + Xmᵀ * diagonal vB * Xm := by
    have hsplit : diagonal (deformSig N σ k T) = diagonal vR + diagonal vB := by
      rw [diagonal_add]
      congr 1
      funext i
      simp only [hvR, hvB, deformSig, hPdef]
      split_ifs <;> ring
    unfold QN
    rw [hsplit, Matrix.mul_add, Matrix.add_mul]
  apply le_antisymm
  · -- `n ≤ d_k`: the rest has norm `< E`, the top block has rank `≤ d_k`
    rw [hQ]
    refine (eigCount_le_add_rank (dff_herm Xm vR) (dff_herm Xm vB) E).trans ?_
    have hvRn : ‖vR‖ ≤ τ⁻¹ := by
      refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hτ.le)).2 fun i => ?_
      simp only [hvR]
      split_ifs
      · simp [hτ.le]
      · rw [Real.norm_eq_abs, abs_of_pos (hσ i)]
        exact hσle i
    have hA : ‖Xmᵀ * diagonal vR * Xm‖ < E :=
      lt_of_le_of_lt ((dff_norm_XDX Xm vR).trans
        (mul_le_mul hvRn hnorm (norm_nonneg _) (inv_nonneg.mpr hτ.le))) hE₁
    rw [eigCount_eq_zero_of_norm_lt (dff_herm Xm vR) hA, zero_add]
    refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans (le_of_eq ?_))
    rw [rank_diagonal, Fintype.card_subtype]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvB]
    split_ifs with hi
    · exact ⟨fun _ => hi, fun _ => (mul_pos hT0 (hσ i)).ne'⟩
    · exact ⟨fun h => absurd rfl h, fun h => absurd h hi⟩
  · -- `n ≥ d_k`: the subspace `{Xᵀu : supp u ⊆ top block}`
    set ι := {i // P i}
    let Pm : Matrix (Fin M) ι ℝ := fun i j => if i = j.1 then 1 else 0
    have hPm : ∀ v : ι → ℝ, ∀ i, ¬ P i → (Pm *ᵥ v) i = 0 := by
      intro v i hi
      simp only [mulVec, dotProduct, Pm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (fun (h : i = j.1) => hi (h ▸ j.2)), zero_mul]
    have hPm' : ∀ v : ι → ℝ, ∀ j : ι, (Pm *ᵥ v) j.1 = v j := by
      intro v j
      simp only [mulVec, dotProduct, Pm]
      rw [Finset.sum_eq_single j (fun j' _ hj' => by
        rw [ite_eq_right (fun h => hj' (Subtype.ext h.symm)), zero_mul])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
    set L := (Xmᵀ * Pm).mulVecLin with hL
    have hLv : ∀ v, L v = Xmᵀ *ᵥ (Pm *ᵥ v) := by
      intro v
      rw [hL, Matrix.mulVecLin_apply, mulVec_mulVec]
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      rw [hLv] at hv
      have h1 := hlow (Pm *ᵥ v) (hPm v)
      rw [hv, dotProduct_zero] at h1
      have h2 : (Pm *ᵥ v) ⬝ᵥ (Pm *ᵥ v) = 0 := by
        have h3 : 0 ≤ (Pm *ᵥ v) ⬝ᵥ (Pm *ᵥ v) := dff_dot_self_nonneg _
        nlinarith
      rw [dotProduct_self_eq_zero] at h2
      funext j
      rw [← hPm' v j, h2]
      rfl
    have hfin : Module.finrank ℝ (LinearMap.range L) =
        (Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0).card := by
      rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
        Fintype.card_subtype]
    rw [← hfin]
    refine eigCount_ge_of_subspace (by unfold QN; exact dff_herm Xm _) _ fun w hw => ?_
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    rw [hLv]
    set u := Pm *ᵥ v with hu
    set w := Xmᵀ *ᵥ u with hw'
    set z := Xm *ᵥ w with hz
    have hu0 : ∀ i, ¬ P i → u i = 0 := hPm v
    -- `⟨w, Q w⟩ = Σ_i σ_i(T) z_i²`
    have hquad : w ⬝ᵥ (QN (diagonal (deformSig N σ k T)) Xm *ᵥ w) =
        ∑ i, z i * (deformSig N σ k T i * z i) := by
      unfold QN
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      simp only [dotProduct, mulVec_diagonal, hz]
    -- `|w|² = ⟨u, z⟩`
    have hww : w ⬝ᵥ w = u ⬝ᵥ z := by
      rw [hz, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, dotProduct_comm]
    set zP : Fin M → ℝ := fun i => if P i then z i else 0 with hzP
    have huz : u ⬝ᵥ z = ∑ i, u i * zP i := by
      simp only [dotProduct, hzP]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · rw [hu0 i hi, zero_mul, zero_mul]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u zP
    have hU : ∑ i, u i ^ 2 = u ⬝ᵥ u := by
      simp only [dotProduct, sq]
    have hlow' : c' * (u ⬝ᵥ u) ≤ w ⬝ᵥ w := hlow u hu0
    set A := w ⬝ᵥ w with hA
    set Z := ∑ i, zP i ^ 2 with hZ
    have hA0 : 0 ≤ A := dff_dot_self_nonneg _
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hUA : A ^ 2 ≤ (u ⬝ᵥ u) * Z := by
      rw [← hU]
      calc A ^ 2 = (∑ i, u i * zP i) ^ 2 := by rw [hww, huz]
        _ ≤ _ := hCS
    -- `c' |w|² ≤ Σ_{top} z_i²`
    have hcA : c' * A ≤ Z := by
      rcases hA0.eq_or_lt with h0 | h0
      · rw [← h0, mul_zero]
        exact hZ0
      · have h1 : c' * A ^ 2 ≤ A * Z := by
          calc c' * A ^ 2 ≤ c' * ((u ⬝ᵥ u) * Z) := mul_le_mul_of_nonneg_left hUA hc'.le
            _ = (c' * (u ⬝ᵥ u)) * Z := by ring
            _ ≤ A * Z := mul_le_mul_of_nonneg_right hlow' hZ0
        have h2 : A * (c' * A) ≤ A * Z := by nlinarith
        exact le_of_mul_le_mul_left h2 h0
    -- `⟨w, Q w⟩ ≥ T s Σ_{top} z_i²`
    have hQZ : T * s * Z ≤ ∑ i, z i * (deformSig N σ k T i * z i) := by
      rw [hZ, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [hzP, deformSig]
      split_ifs with hi
      · have := htop i hi
        have h1 : T * s ≤ T * σ i := mul_le_mul_of_nonneg_left this hT0.le
        nlinarith [sq_nonneg (z i)]
      · rw [sq, mul_zero, mul_zero]
        nlinarith [sq_nonneg (z i), hσ i]
    rw [hquad]
    calc E * A ≤ T * s * c' * A := mul_le_mul_of_nonneg_right hE₂ hA0
      _ = T * s * (c' * A) := by ring
      _ ≤ T * s * Z := mul_le_mul_of_nonneg_left hcA (by positivity)
      _ ≤ _ := hQZ

/-- `‖Q(t) − Q(s)‖ ≤ τ⁻¹ ‖XᵀX‖ |t − s|` along the deformation `Σ(t)` of Lemma 10.4. -/
theorem QN_deform_lip {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i) {τ C₀ : ℝ} (hτ : 0 < τ)
    (hσle : ∀ i, σ i ≤ τ⁻¹)
    (k : ℕ) (Xm : Matrix (Fin M) (Fin N) ℝ) (hnorm : ‖Xmᵀ * Xm‖ ≤ C₀) {t s : ℝ} (ht : 1 ≤ t)
    (hs : 1 ≤ s) :
    ‖QN (diagonal (deformSig N σ k t)) Xm - QN (diagonal (deformSig N σ k s)) Xm‖ ≤
      τ⁻¹ * C₀ * |t - s| := by
  unfold QN
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  refine (dff_norm_XDX Xm _).trans ?_
  have hτi : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hv : ‖deformSig N σ k t - deformSig N σ k s‖ ≤ τ⁻¹ * |t - s| := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hτi (abs_nonneg _))).2 fun i => ?_
    simp only [Pi.sub_apply, deformSig]
    split_ifs
    · rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_pos (hσ i), mul_comm]
      exact mul_le_mul_of_nonneg_right (hσle i) (abs_nonneg _)
    · rw [sub_self, norm_zero]
      exact mul_nonneg hτi (abs_nonneg _)
  calc _ ≤ τ⁻¹ * |t - s| * C₀ :=
        mul_le_mul hv hnorm (norm_nonneg _) (mul_nonneg hτi (abs_nonneg _))
    _ = τ⁻¹ * C₀ * |t - s| := by ring

/-! ## A concrete instance: `M = 2`, `N = 20`, `σ = (10, 1)`, `τ = 1/10`

Here `p = 2`, `x_3 ∈ (-0.82, -0.8)`, `x_2 ∈ (-0.13, -0.128)`, so that `a_2 ≥ 5.9` and
`a_3 ≤ 1.5`. -/

section Instance

open Polynomial

end Instance

/-! ## Compiled instances of the statements above

`M = 2`, `N = 20`, `σ = (10, 1)`, `τ = 1/10`, `k = 1` (so `p = 2`), `τ_g = 4`; for the matrix
statements `X` has the rows `e_1ᵀ, e_2ᵀ` of `ℝ²⁰` and `C₀ = 1`. -/

#print axioms deform_facts
#print axioms deformE_ge_gapMid
#print axioms deform_end
#print axioms eigCount_deform_end
#print axioms QN_deform_lip

end Anisotropic
