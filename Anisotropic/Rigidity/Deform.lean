module

public import Anisotropic.Density.Basic
public import Anisotropic.Density.Boundary
public import Anisotropic.Density.Critical
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Density.Stability.Domains
public import Anisotropic.Density.Varrho
public import Anisotropic.Framework.Model
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The deformation `Σ(t)` of Lemma 10.4 (deterministic): the middle of the gap, its windows, the top block -/

/-- The deformation `σ(t)` of the proof of Lemma 10.4: the top block `{i : −σ_i⁻¹ > x_{2k}}`
(of size `d_k`) is multiplied by `t`. -/
def deformSig (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) (t : ℝ) : Fin M → ℝ :=
  fun i => if 1 + σ i * xCrit N σ (2 * k) < 0 then t * σ i else σ i

/-- `x_mid = m(θ_k)` at the gap midpoint `θ_k`. -/
def xMid (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  (mExt N σ (gapMid N σ k)).re

/-- The moving threshold `E_t = f_t(x_mid)`. -/
def deformE (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  fR N (deformSig N σ k t) (xMid N σ k)

/-- `C_x = C_m(τ_x)`, `τ_x = min(τ_g/2, κ_max(τ)⁻¹)`: bounds `|x_{2k}|`, `|x_mid|`, `1/σ_i` on the
top block. -/
def gapCx (τ τg : ℝ) : ℝ :=
  mBoundConst (min (τg / 2) (kappaMax τ)⁻¹)

/-- The Lipschitz constant `4 C_x⁵ / τ_g²` of `t ↦ E_t`. -/
def deformL (τ τg : ℝ) : ℝ :=
  4 * gapCx τ τg ^ 5 / τg ^ 2

/-- The bound `C_x + 2 τ⁻¹ C_x² / τ_g` on `E_t`. -/
def deformEmax (τ τg : ℝ) : ℝ :=
  gapCx τ τg + 2 * τ⁻¹ * gapCx τ τg ^ 2 / τg

/-! ## Elementary facts under the density assumptions -/

private lemma dfm_empMeasure_apply (σ : Fin M → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empMeasure σ s = (M : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun i => σ i ∈ s).card : ℝ≥0∞) := by
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- Under the density assumptions, `N > 0` and some `σ_i` is positive. -/
private lemma dfm_facts {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
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
  rw [dfm_empMeasure_apply σ measurableSet_Icc] at hgap
  simp only [hall, Set.mem_Icc, le_refl, h.pos.le, and_self, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] at hgap
  have hM' : (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)
  rw [hM', ENNReal.toReal_one] at hgap
  linarith [h.pos]

/-- `a_j ≤ a_i` for `1 ≤ i ≤ j ≤ 2p`. -/
private lemma dfm_edgeVal_anti {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 2 * numBands N σ) :
    edgeVal N σ j ≤ edgeVal N σ i := by
  obtain ⟨hN, hS⟩ := dfm_facts h
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (edgeVal_succ_le N σ h.nonneg hN hS (le_trans hi hij) (by omega)).trans (ih (by omega))

/-- `0 ≤ a_j` for `1 ≤ j ≤ 2p`. -/
private lemma dfm_edgeVal_nonneg {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 2 * numBands N σ) : 0 ≤ edgeVal N σ j := by
  obtain ⟨hN, hS⟩ := dfm_facts h
  exact (edgeVal_mem_Icc N σ h.nonneg hN hS h.pos h.phi_lower h.phi_upper h.bound_Sigma hj1
    hj).1

/-- The points of `supp ϱ`: the atom `0` and the bands `[a_{2l}, a_{2l−1}]`, `1 ≤ l ≤ p`. -/
private lemma dfm_mem_support {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {s : ℝ}
    (hs : s ∈ (varrho N σ).support) :
    s = 0 ∨ ∃ l, 1 ≤ l ∧ l ≤ numBands N σ ∧ edgeVal N σ (2 * l) ≤ s ∧
      s ≤ edgeVal N σ (2 * l - 1) := by
  obtain ⟨hN, hS⟩ := dfm_facts h
  have hsub : (varrho N σ).support ⊆ Set.Icc 0 (edgeVal N σ 1) :=
    Measure.support_subset_of_isClosed isClosed_Icc
      (mem_ae_iff.mpr (varrho_compl_Icc_edgeVal N σ h.nonneg hN hS))
  rcases (hsub hs).1.eq_or_lt with h0 | hpos
  · exact Or.inl h0.symm
  · obtain ⟨l, hl1, hlp, hmem⟩ := (mem_support_varrho_iff N σ h.nonneg hN hS hpos).1 hs
    exact Or.inr ⟨l, hl1, hlp, hmem.1, hmem.2⟩

private lemma dfm_support_nonempty {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    (varrho N σ).support.Nonempty := by
  obtain ⟨hN, -⟩ := dfm_facts h
  have := isProbabilityMeasure_varrho N σ h.nonneg hN
  exact Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)

/-! ## The critical points `x_1 ≥ ⋯ ≥ x_{2p−1}` and the poles between them -/

section CritPoints

open Polynomial

private lemma dfm_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma dfm_mem_posVals (σ : Fin M → ℝ) {i : Fin M} (hi : 0 < σ i) : σ i ∈ posVals σ := by
  simp [posVals, hi]

private lemma dfm_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma dfm_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (dfm_mem_posVals σ hpos)

/-- For `s > 0`: `-1/s < x ↔ 0 < 1 + s x`. -/
private lemma dfm_lt_iff {s x : ℝ} (hs : 0 < s) : -s⁻¹ < x ↔ 0 < 1 + s * x := by
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
private lemma dfm_gt_iff {s x : ℝ} (hs : 0 < s) : x < -s⁻¹ ↔ 1 + s * x < 0 := by
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

private lemma dfm_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma dfm_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := dfm_pos_of_mem σ hu
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
    (mul_ne_zero (mul_ne_zero (dfm_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

/-- A point of `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)` is negative, lies in `(-s_n⁻¹, 0)`, is not a pole, and
is a critical point of `f`. -/
private lemma dfm_mem_innerCrit (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {x : ℝ} (hx : x ∈ innerCrit N σ) :
    InInner σ x ∧ (∀ u ∈ posVals σ, 1 + u * x ≠ 0) ∧ fR1 N σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, mem_roots (dfm_critPoly_ne_zero N σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly N σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := dfm_pos_of_mem σ hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact dfm_critPoly_pole N σ hN hu h0
  refine ⟨hin, hnp, ?_⟩
  rw [critPoly_eval N σ hσ hin.1.ne (dfm_nonpole_all σ hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma dfm_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
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
      have ih := dfm_list_prefix y L hpw.2 j hj
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

private lemma dfm_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
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
  · rw [dfm_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

/-- The number of critical points in `(y, 0)`, counted with multiplicity. -/
private def dfmA (N : ℕ) (σ : Fin M → ℝ) (y : ℝ) : ℕ :=
  Multiset.card ((innerCrit N σ).filter (fun x => y < x))

/-- `x_k ∈ 𝒞` for `1 ≤ k < 2p`, and `y < x_k` iff at least `k` critical points lie in
`(y, 0)`. -/
private lemma dfm_xCrit_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ ∧ ∀ y, (y < xCrit N σ k ↔ k ≤ dfmA N σ y) := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hx : xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := dfm_sort_spec (innerCrit N σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y, dfmA]
  omega

private lemma dfm_xCrit_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k k' : ℕ} (hk1 : 1 ≤ k) (hkk : k ≤ k')
    (hk' : k' < 2 * numBands N σ) : xCrit N σ k' ≤ xCrit N σ k := by
  by_contra h
  rw [not_le] at h
  have h1 := ((dfm_xCrit_spec N σ hσ hN hS (k := k') (by omega) hk').2 (xCrit N σ k)).1 h
  have h2 := ((dfm_xCrit_spec N σ hσ hN hS hk1 (by omega)).2 (xCrit N σ k)).2 (by omega)
  exact lt_irrefl _ h2

/-- `x_k < 0` for `1 ≤ k < 2p`, and `x_k` is not a pole. -/
private lemma dfm_xCrit_good (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k < 0 ∧ (∀ i, 1 + σ i * xCrit N σ k ≠ 0) ∧ fR1 N σ (xCrit N σ k) = 0 := by
  obtain ⟨hin, hnp, h1⟩ :=
    dfm_mem_innerCrit N σ hσ hN (dfm_xCrit_spec N σ hσ hN hS hk1 hk).1
  exact ⟨hin.1, dfm_nonpole_all σ hσ hnp, h1⟩

/-- An odd number of critical points lies to the right of every pole `-1/s` (Lemma 2.4: one in
`I_1`, an even number in each other `I_l`). -/
private lemma dfm_A_odd (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (n : ℕ) :
    ∀ s ∈ posVals σ, ((posVals σ).filter (fun u => s < u)).card = n →
      Odd (dfmA N σ (-s⁻¹)) := by
  have hS' : ∀ s ∈ posVals σ, (posVals σ).Nonempty := fun s hs => ⟨s, hs⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    have hs0 := dfm_pos_of_mem σ hs
    by_cases hne : ((posVals σ).filter (fun u => s < u)).Nonempty
    · set s' := ((posVals σ).filter (fun u => s < u)).min' hne with hs'def
      have hm := Finset.min'_mem _ hne
      rw [← hs'def] at hm
      obtain ⟨hs'S, hss'⟩ := Finset.mem_filter.mp hm
      have hs'0 := dfm_pos_of_mem σ hs'S
      have hcons : ∀ u ∈ posVals σ, ¬ (s < u ∧ u < s') := by
        rintro u hu ⟨h1, h2⟩
        have := Finset.min'_le _ u (Finset.mem_filter.mpr ⟨hu, h1⟩)
        rw [← hs'def] at this
        linarith
      have hinv : -s⁻¹ < -s'⁻¹ := neg_lt_neg (inv_strictAnti₀ hs0 hss')
      have hsplit : dfmA N σ (-s⁻¹) =
          Multiset.card ((innerCrit N σ).filter (fun x => -s⁻¹ < x ∧ x < -s'⁻¹)) +
            dfmA N σ (-s'⁻¹) := by
        unfold dfmA
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
          have hnp := (dfm_mem_innerCrit N σ hσ hN hx).2.1 s' hs'S
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
        have hx0 := (dfm_mem_innerCrit N σ hσ hN hx).1.1
        rw [dfm_lt_iff hs0]
        constructor
        · intro h u hu
          have := mul_le_mul_of_nonpos_right (hmax u hu) hx0.le
          linarith
        · intro h
          exact h s hs
      unfold dfmA
      rw [e, card_innerCrit_I1 N σ hσ hN (hS' s hs)]
      exact odd_one

end CritPoints

/-! ## A concrete instance: `M = 2`, `N = 20`, `σ = (10, 1)`, `τ = 1/10`

Here `p = 2`, `x_3 ∈ (-0.82, -0.8)`, `x_2 ∈ (-0.13, -0.128)`, `y_4 = 1/x_4 ∈ (-0.78, -0.76)`, so
that `a_2 ≥ 5.9`, `a_3 ≤ 1.5` and `a_4 ≥ 1/2`. -/

section Instance

open Polynomial

end Instance

/-- The window `[θ_k − τ_g/4, θ_k + τ_g/4]` around the gap midpoint stays at distance `≥ τ_g/4`
from `supp ϱ`. -/
theorem gapMid_window {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hτg : 0 < τg)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ) (ha : τg ≤ edgeVal N σ (2 * k))
    (hg : τg ≤ edgeVal N σ (2 * k) - edgeVal N σ (2 * k + 1)) :
    τg / 2 ≤ gapMid N σ k ∧
      ∀ E ∈ Set.Icc (gapMid N σ k - τg / 4) (gapMid N σ k + τg / 4),
        τg / 4 ≤ Metric.infDist E (varrho N σ).support := by
  have hp := hkp
  have h0 : 0 ≤ edgeVal N σ (2 * k + 1) := dfm_edgeVal_nonneg h (by omega) (by omega)
  have hsplit : ∀ s ∈ (varrho N σ).support,
      s ≤ edgeVal N σ (2 * k + 1) ∨ edgeVal N σ (2 * k) ≤ s := by
    intro s hs
    rcases dfm_mem_support h hs with rfl | ⟨l, hl1, hlp, hl, hl'⟩
    · exact Or.inl h0
    · rcases le_or_gt l k with hlk | hlk
      · exact Or.inr ((dfm_edgeVal_anti h (by omega) (by omega) (by omega)).trans hl)
      · exact Or.inl (hl'.trans (dfm_edgeVal_anti h (by omega) (by omega) (by omega)))
  refine ⟨by unfold gapMid; linarith, fun E hE => ?_⟩
  rw [Metric.le_infDist (dfm_support_nonempty h)]
  intro s hs
  unfold gapMid at hE
  rw [Real.dist_eq]
  rcases hsplit s hs with hs' | hs'
  · rw [abs_of_nonneg (by linarith [hE.1])]
    linarith [hE.1]
  · rw [abs_of_nonpos (by linarith [hE.2])]
    linarith [hE.2]

/-- The window around `a_{2p}/2` stays at distance `≥ τ_g/4` from `supp ϱ` (including the atom
at `0`). -/
theorem bottom_window {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hτg : 0 < τg)
    (ha : τg ≤ edgeVal N σ (2 * numBands N σ)) :
    ∀ E ∈ Set.Icc (edgeVal N σ (2 * numBands N σ) / 2 - τg / 4)
        (edgeVal N σ (2 * numBands N σ) / 2 + τg / 4),
      τg / 4 ≤ Metric.infDist E (varrho N σ).support := by
  have hp := (card_innerCrit N σ h.nonneg (dfm_facts h).1 (dfm_facts h).2).2
  intro E hE
  rw [Metric.le_infDist (dfm_support_nonempty h)]
  intro s hs
  rw [Real.dist_eq]
  rcases dfm_mem_support h hs with rfl | ⟨l, hl1, hlp, hl, -⟩
  · rw [sub_zero, abs_of_nonneg (by linarith [hE.1])]
    linarith [hE.1]
  · have := (dfm_edgeVal_anti h (i := 2 * l) (by omega) (by omega) le_rfl).trans hl
    rw [abs_of_nonpos (by linarith [hE.2])]
    linarith [hE.2]

/-- The top block `{i : −σ_i⁻¹ > x_{2k}}` has `d_k` elements. -/
theorem topBlock_card {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) {k : ℕ}
    (hk : 1 ≤ k) (hkp : k < numBands N σ) :
    (Finset.univ.filter fun i => 1 + σ i * xCrit N σ (2 * k) < 0).card = cumCount N σ k := by
  obtain ⟨hN, hS⟩ := dfm_facts h
  have hσ := h.nonneg
  have hk2 : 2 * k < 2 * numBands N σ := by omega
  have hspec := fun {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 2 * numBands N σ) =>
    (dfm_xCrit_spec N σ hσ hN hS hm1 hm).2
  have hgood := fun {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 2 * numBands N σ) =>
    dfm_xCrit_good N σ hσ hN hS hm1 hm
  -- the index `l` of the band of the pole `-σ_j⁻¹`: `2l − 1` critical points lie to its right
  set g : Fin M → ℕ := fun j => (dfmA N σ (-(σ j)⁻¹) + 1) / 2 with hg
  have hodd : ∀ j, 0 < σ j → ∃ c, dfmA N σ (-(σ j)⁻¹) = 2 * c + 1 := fun j hj =>
    dfm_A_odd N σ hσ hN _ (σ j) (dfm_mem_posVals σ hj) rfl
  have hne : ∀ j, 0 < σ j → ∀ m, 1 ≤ m → m < 2 * numBands N σ → -(σ j)⁻¹ ≠ xCrit N σ m := by
    intro j hj m hm1 hm he
    apply (hgood hm1 hm).2.1 j
    rw [← he]
    field_simp
    ring
  have hpos_of : ∀ j, 1 + σ j * xCrit N σ (2 * k) < 0 → 0 < σ j := by
    intro j hj
    rcases (hσ j).eq_or_lt with h0 | h0
    · rw [← h0] at hj; norm_num at hj
    · exact h0
  have hmaps : ∀ j ∈ Finset.univ.filter (fun i => 1 + σ i * xCrit N σ (2 * k) < 0),
      g j ∈ Finset.Icc 1 k := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have hj0 := hpos_of j hj'
    obtain ⟨c, hc⟩ := hodd j hj0
    have hlt : xCrit N σ (2 * k) < -(σ j)⁻¹ := (dfm_gt_iff hj0).2 hj'
    have hA : dfmA N σ (-(σ j)⁻¹) < 2 * k := by
      by_contra h'
      have := (hspec (m := 2 * k) (by omega) hk2 _).2 (not_lt.mp h')
      linarith
    rw [Finset.mem_Icc, hg]
    simp only
    rw [hc] at hA ⊢
    omega
  have hfib : ∀ l ∈ Finset.Icc 1 k,
      (Finset.univ.filter (fun i => 1 + σ i * xCrit N σ (2 * k) < 0)).filter (fun j => g j = l) =
        Finset.univ.filter (fun j =>
          xCrit N σ (2 * l) ≤ -(σ j)⁻¹ ∧ -(σ j)⁻¹ ≤ xCrit N σ (2 * l - 1)) := by
    intro l hl
    obtain ⟨hl1, hlk⟩ := Finset.mem_Icc.mp hl
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hgj⟩
      have hj0 := hpos_of j hj
      obtain ⟨c, hc⟩ := hodd j hj0
      have hAl : dfmA N σ (-(σ j)⁻¹) = 2 * l - 1 := by
        rw [hg] at hgj
        simp only at hgj
        rw [hc] at hgj ⊢
        omega
      refine ⟨not_lt.mp fun h' => ?_, le_of_lt ?_⟩
      · have := (hspec (m := 2 * l) (by omega) (by omega) _).1 h'
        omega
      · exact (hspec (m := 2 * l - 1) (by omega) (by omega) _).2 (by omega)
    · rintro ⟨h1, h2⟩
      have hj0 : 0 < σ j := by
        rcases (hσ j).eq_or_lt with h0 | h0
        · rw [← h0, _root_.inv_zero, neg_zero] at h2
          linarith [(hgood (m := 2 * l - 1) (by omega) (by omega)).1]
        · exact h0
      have h1' : xCrit N σ (2 * l) < -(σ j)⁻¹ :=
        lt_of_le_of_ne h1 (hne j hj0 (2 * l) (by omega) (by omega)).symm
      have h2' : -(σ j)⁻¹ < xCrit N σ (2 * l - 1) :=
        lt_of_le_of_ne h2 (hne j hj0 (2 * l - 1) (by omega) (by omega))
      have hA1 := (hspec (m := 2 * l - 1) (by omega) (by omega) _).1 h2'
      have hA2 : dfmA N σ (-(σ j)⁻¹) < 2 * l := by
        by_contra h'
        have := (hspec (m := 2 * l) (by omega) (by omega) _).2 (not_lt.mp h')
        linarith
      refine ⟨?_, ?_⟩
      · have hanti := dfm_xCrit_anti N σ hσ hN hS (k := 2 * l) (k' := 2 * k) (by omega)
          (by omega) hk2
        exact (dfm_gt_iff hj0).1 (by linarith)
      · rw [hg]
        simp only
        omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl fun l hl => congrArg Finset.card (hfib l hl)]
  have hband : ∀ l ∈ Finset.Icc 1 k, bandCount N σ l = ((Finset.univ.filter (fun j =>
      xCrit N σ (2 * l) ≤ -(σ j)⁻¹ ∧ -(σ j)⁻¹ ≤ xCrit N σ (2 * l - 1))).card : ℝ) :=
    fun l hl => bandCount_eq_card N σ hσ hN hS (Finset.mem_Icc.mp hl).1
      (lt_of_le_of_lt (Finset.mem_Icc.mp hl).2 hkp)
  unfold cumCount
  rw [Finset.sum_congr rfl hband, ← Nat.cast_sum, Nat.floor_natCast]

/-- Real points lie in the closure of `ℂ₊`. -/
private lemma dfm_neBot (E : ℝ) : (𝓝[upperHalf] (E : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
  simp

/-- Lemma 4.10 at a real point `E > 0` of `[τ', τ'⁻¹]`, as the limit from `ℂ₊`:
`|m(E + i0)| ≤ C(τ')`. -/
private lemma dfm_norm_mExt_le {τ' : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ' N σ) {E : ℝ}
    (hE : τ' < E) (hE' : E < τ'⁻¹) : ‖mExt N σ E‖ ≤ genPropConst τ' := by
  have hE0 : 0 < E := lt_trans h.pos hE
  have := dfm_neBot E
  have ht := (tendsto_mFun_of_ne_zero N σ h.nonneg hE0.ne').norm
  have hopen : IsOpen {z : ℂ | τ' < ‖z‖ ∧ ‖z‖ < τ'⁻¹} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hmem : (E : ℂ) ∈ {z : ℂ | τ' < ‖z‖ ∧ ‖z‖ < τ'⁻¹} := by
    simp only [Set.mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0]
    exact ⟨hE, hE'⟩
  have hev : ∀ᶠ z in 𝓝[upperHalf] (E : ℂ), ‖mFun N σ z‖ ≤ genPropConst τ' := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem),
      self_mem_nhdsWithin] with z hz hz'
    exact (gen_prop_m h hz' hz.1.le hz.2.le).2.1
  exact le_of_tendsto ht hev

/-- `d_k ≤ (1 − τ/C_x) N` and `σ_i ≥ C_x⁻¹` on the top block (proof of Lemma 10.4). -/
theorem topBlock_bounds {τ τg : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hτg : 0 < τg) {k : ℕ} (hk : 1 ≤ k) (hkp : k < numBands N σ)
    (ha : τg ≤ edgeVal N σ (2 * k)) :
    (cumCount N σ k : ℝ) ≤ (1 - τ / gapCx τ τg) * N ∧
      ∀ i, 1 + σ i * xCrit N σ (2 * k) < 0 → (gapCx τ τg)⁻¹ ≤ σ i := by
  obtain ⟨hN, hS⟩ := dfm_facts h
  have hσ := h.nonneg
  have hτ := h.pos
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hτ1 : τ ≤ 1 := by
    have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_of_not_ge hc)
    linarith
  -- the constants `τ_x = min(τ_g/2, κ_max⁻¹)`, `τ' = τ_x/2`, `C_x = C(τ')`
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
  have hCpos : 0 < genPropConst τ' := by unfold genPropConst; positivity
  -- `x = x_{2k} = m(a_{2k})`, with `|x_{2k}| ≤ C_x`
  have hk2 : 2 * k < 2 * numBands N σ := by omega
  obtain ⟨hx0, hxnp, hx1⟩ := dfm_xCrit_good N σ hσ hN hS (k := 2 * k) (by omega) hk2
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
  have hbound : -xCrit N σ (2 * k) ≤ gapCx τ τg := by
    have := dfm_norm_mExt_le (h.mono hτ'pos hτ'τ) hlow hup
    rw [hma, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx0] at this
    rw [hC]
    exact this
  set x := xCrit N σ (2 * k) with hxdef
  set u := -x with hu
  have hupos : 0 < u := by linarith
  -- on the top block, `σ_i u > 1`
  have htop : ∀ i, 1 + σ i * x < 0 → 0 < σ i ∧ 1 < σ i * u := by
    intro i hi
    rcases (hσ i).eq_or_lt with h0 | h0
    · rw [← h0] at hi; norm_num at hi
    · exact ⟨h0, by rw [hu]; linarith⟩
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← topBlock_card h hk hkp]
    set T := Finset.univ.filter fun i => 1 + σ i * x < 0 with hT
    rcases Nat.eq_zero_or_pos T.card with hd | hd
    · rw [hd, Nat.cast_zero]
      refine mul_nonneg ?_ (Nat.cast_nonneg N)
      rw [sub_nonneg, div_le_one (hC ▸ hCpos), hC]
      unfold genPropConst
      rw [le_div_iff₀ (by positivity)]
      have h4 : τ' ^ 4 ≤ 1 := pow_le_one₀ hτ'pos.le (hτ'τ.trans hτ1)
      nlinarith [pow_pos hτ'pos 4]
    · obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hd
      have hi₀' := htop i₀ (Finset.mem_filter.mp hi₀).2
      have huτ : τ < u := by
        have := h.bound_Sigma i₀
        have h5 : σ i₀ * u ≤ τ⁻¹ * u := mul_le_mul_of_nonneg_right this hupos.le
        have h6 : 1 < τ⁻¹ * u := lt_of_lt_of_le hi₀'.2 h5
        rw [lt_inv_mul_iff₀ hτ] at h6
        linarith
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have huτ' : 0 < u - τ := by linarith
      -- `f'(x_{2k}) = 0`: `x⁻² = N⁻¹ Σ_i σ_i² (1 + σ_i x)⁻²`
      have hsum : ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) = (x ^ 2)⁻¹ := by
        unfold fR1 at hx1
        linarith
      have hterm : ∀ i ∈ T, 1 / (N * (u - τ) ^ 2) ≤ σ i ^ 2 / (N * (1 + σ i * x) ^ 2) := by
        intro i hi
        obtain ⟨hi0, hiu⟩ := htop i (Finset.mem_filter.mp hi).2
        have hστ : σ i * τ ≤ 1 := by
          have := mul_le_mul_of_nonneg_right (h.bound_Sigma i) hτ.le
          rwa [inv_mul_cancel₀ hτ.ne'] at this
        have hw : 0 < σ i * u - 1 := by linarith
        have hw' : σ i * u - 1 ≤ σ i * (u - τ) := by nlinarith
        have hsq : (1 + σ i * x) ^ 2 ≤ σ i ^ 2 * (u - τ) ^ 2 := by
          have e : (1 + σ i * x) ^ 2 = (σ i * u - 1) ^ 2 := by rw [hu]; ring
          rw [e, show σ i ^ 2 * (u - τ) ^ 2 = (σ i * (u - τ)) ^ 2 by ring]
          exact pow_le_pow_left₀ hw.le hw' 2
        have hpos1 : 0 < (1 + σ i * x) ^ 2 := by
          have := hxnp i
          positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hge : (T.card : ℝ) / (N * (u - τ) ^ 2) ≤ (x ^ 2)⁻¹ := by
        rw [← hsum]
        calc (T.card : ℝ) / (N * (u - τ) ^ 2) = ∑ i ∈ T, 1 / (N * (u - τ) ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ∑ i ∈ T, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) := Finset.sum_le_sum hterm
          _ ≤ ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun i _ _ => by positivity)
      have hx2 : x ^ 2 = u ^ 2 := by rw [hu]; ring
      rw [hx2] at hge
      -- `d_k ≤ N (1 − τ/u)² ≤ N (1 − τ/u) ≤ N (1 − τ/C_x)`
      have hd1 : (T.card : ℝ) ≤ N * (u - τ) ^ 2 / u ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at hge
        calc (T.card : ℝ) ≤ (u ^ 2)⁻¹ * (N * (u - τ) ^ 2) := hge
          _ = N * (u - τ) ^ 2 / u ^ 2 := by ring
      have e1 : (N : ℝ) * (u - τ) ^ 2 / u ^ 2 = N * (1 - τ / u) ^ 2 := by field_simp
      have h7 : τ / gapCx τ τg ≤ τ / u := div_le_div_of_nonneg_left hτ.le hupos hbound
      have h8 : 0 ≤ 1 - τ / u := by rw [sub_nonneg, div_le_one hupos]; linarith
      have h9 : 0 ≤ τ / u := by positivity
      have h10 : (1 - τ / u) ^ 2 ≤ 1 - τ / gapCx τ τg := by nlinarith
      calc (T.card : ℝ) ≤ N * (1 - τ / u) ^ 2 := e1 ▸ hd1
        _ ≤ N * (1 - τ / gapCx τ τg) := mul_le_mul_of_nonneg_left h10 hNr.le
        _ = (1 - τ / gapCx τ τg) * N := mul_comm _ _
  · obtain ⟨hi0, hiu⟩ := htop i hi
    rw [inv_le_iff_one_le_mul₀' (hC ▸ hCpos)]
    nlinarith

/-- Assumption 2.1 for `Σ(t)`, `t ∈ [1, T]`, at the parameter `min(τ, τ/T)`. -/
theorem isModel_deform {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hm : IsModel τ C M N (diagonal σ) X) (k : ℕ)
    {t T : ℝ} (ht : 1 ≤ t) (htT : t ≤ T) :
    IsModel (min τ (τ / T)) C M N (diagonal (deformSig N σ k t)) X := by
  have hd := diagModel_iff.mpr hm
  refine diagModel_iff.mp ?_
  have hT : 0 < T := by linarith
  have hσ' : ∀ i, σ i ≤ deformSig N σ k t i ∧ deformSig N σ k t i ≤ T * σ i := by
    intro i
    have hi := hd.pos i
    unfold deformSig
    split_ifs
    · exact ⟨by nlinarith, by nlinarith⟩
    · exact ⟨le_rfl, by nlinarith⟩
  -- the case `M = 0` is vacuous; otherwise `τ > 0`
  rcases isEmpty_or_nonempty (Fin M) with hE | ⟨⟨i₀⟩⟩
  · have hM : M = 0 := by simpa using hE
    have hτ0 : 0 ≤ τ := by
      by_contra hneg
      have := hd.ratio_le
      have : (0 : ℝ) ≤ (M : ℝ) / N := by positivity
      have : τ⁻¹ < 0 := inv_lt_zero.mpr (lt_of_not_ge hneg)
      linarith
    have hmin : min τ (τ / T) ≤ τ := min_le_left _ _
    rcases hτ0.eq_or_lt with h0 | hpos
    · rw [← h0, zero_div, min_self]
      rw [← h0] at hd
      exact ⟨hd.ratio_ge, hd.ratio_le, hd.entries, fun i => hE.elim i, fun i => hE.elim i,
        by simp [Set.eq_empty_of_isEmpty, hM]⟩
    · have hτ' : 0 < min τ (τ / T) := lt_min hpos (div_pos hpos hT)
      refine ⟨hmin.trans hd.ratio_ge, hd.ratio_le.trans (inv_anti₀ hτ' hmin), hd.entries,
        fun i => hE.elim i, fun i => hE.elim i, by simp [Set.eq_empty_of_isEmpty, hM]⟩
  · have hτ : 0 < τ := by
      by_contra hneg
      have h1 := hd.le i₀
      have h2 := hd.pos i₀
      have : τ⁻¹ ≤ 0 := inv_nonpos.mpr (not_lt.mp hneg)
      linarith
    have hmin : min τ (τ / T) ≤ τ := min_le_left _ _
    have hτ' : 0 < min τ (τ / T) := lt_min hτ (div_pos hτ hT)
    have hinv : (τ / T)⁻¹ ≤ (min τ (τ / T))⁻¹ := inv_anti₀ hτ' (min_le_right _ _)
    refine ⟨hmin.trans hd.ratio_ge, hd.ratio_le.trans (inv_anti₀ hτ' hmin), hd.entries,
      fun i => lt_of_lt_of_le (hd.pos i) (hσ' i).1, fun i => ?_, ?_⟩
    · refine (hσ' i).2.trans (le_trans ?_ hinv)
      rw [inv_div]
      have := hd.le i
      rw [le_div_iff₀ hτ]
      calc T * σ i * τ = T * (σ i * τ) := by ring
        _ ≤ T * 1 := by
          apply mul_le_mul_of_nonneg_left _ hT.le
          have := mul_le_mul_of_nonneg_right this hτ.le
          rwa [inv_mul_cancel₀ hτ.ne'] at this
        _ = T := mul_one T
    · have hsub : {i | deformSig N σ k t i ∈ Set.Icc 0 (min τ (τ / T))} ⊆
          {i | σ i ∈ Set.Icc 0 τ} := by
        intro i hi
        exact ⟨(hd.pos i).le, (hσ' i).1.trans (hi.2.trans hmin)⟩
      calc ({i | deformSig N σ k t i ∈ Set.Icc 0 (min τ (τ / T))}.ncard : ℝ)
          ≤ ({i | σ i ∈ Set.Icc 0 τ}.ncard : ℝ) := by
            exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (1 - τ) * M := hd.gap
        _ ≤ (1 - min τ (τ / T)) * M := by
            apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg M)
            linarith

/-! ## Compiled instances of the statements above

`M = 2`, `N = 20`, `σ = (10, 1)`, `τ = 1/10`, `k = 1` (so `p = 2`), and for the model the
Rademacher matrix with `Σ = diag(30, 1)`, `τ = 1/30`, `t = 2`, `T = 3`. -/

end Anisotropic
