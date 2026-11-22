module

public import Anisotropic.MainDefs
public import Anisotropic.Density.Structure

@[expose] public section

/-!
# Band counts `N_k` (Lemma A.1) and regularity (Definition 2.7)

`N_k = N ϱ([a_{2k}, a_{2k-1}])`, (def_N_k). Lemma A.1, in the general-rank form
(`σ ≥ 0`, `rank Σ = #{i | σ_i > 0}`): `N ϱ({0}) = (N - rank Σ)₊`,
`Σ_{k=1}^p N_k = N ∧ rank Σ` (Ni_sum), and for `k = 1, …, p - 1`,
`N_k = #{j | x_{2k} ≤ -σ_j⁻¹ ≤ x_{2k-1}}` (Ni_rep); every `N_k` is a natural number.
Definition 2.7: regular edges (reg: edge) and regular bulk components.

Proofs (Appendix A.1).
* The atom: `ϱ = (1 - R)₊ δ₀ + ρ dx` on `(0, ∞)`.
* (Ni_rep): on a band `[a, b] = [a_{2k}, a_{2k-1}] ⊂ (0, ∞)`, `k < p`, put
  `Φ(w) = w f(w) + log w - N⁻¹ Σ_{σ_i > 0} log(w + σ_i⁻¹)` (principal logarithm). Then
  `Φ' = w f'(w)`, and on the open band `m` is the holomorphic local inverse of `f` at
  `m(E) ∈ ℂ₊`, so `E ↦ Φ(m(E))` has derivative `m(E)`. It is continuous on `[a, b]`, where
  `m(a) = x_{2k}` and `m(b) = x_{2k-1}` are negative reals off the poles. The fundamental
  theorem of calculus and `Im log x = π 1[x < 0]` for real `x ≠ 0` give
  `π ϱ([a, b]) = Im ∫_a^b m = π N⁻¹ #{i | σ_i > 0, x_{2k} ≤ -σ_i⁻¹ ≤ x_{2k-1}}`.
* (Ni_sum): consecutive bands meet in points `a_{2k} > 0` without mass, `ϱ` vanishes on
  `(0, ∞)` off the bands (Lemma 2.6), and `a_{2p} = y_{2p}² Σ_s r_s s (y_{2p} + s)⁻² > 0` unless
  `y_{2p} = 0`, i.e. `R = 1`, in which case the atom vanishes. Hence
  `Σ_k N_k = N ϱ((0, ∞)) = N min(1, R)`.
* Integrality: `N_p = N ∧ rank Σ - Σ_{k < p} N_k`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## The measure `ϱ` on points, on `(0, ∞)` and on bands -/

private lemma cnt_withDensity_singleton (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) :
    ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x => ENNReal.ofReal (rhoDens N σ x))) {x} = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)

private lemma cnt_varrho_singleton (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) :
    varrho N σ {x} = if x = 0 then ENNReal.ofReal (max (1 - massRatio N σ) 0) else 0 := by
  rw [varrho, Measure.add_apply, cnt_withDensity_singleton, add_zero, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton x)]
  split_ifs with h
  · subst h; simp
  · simp [Ne.symm h]

private lemma cnt_varrho_singleton_pos (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x ≠ 0) :
    varrho N σ {x} = 0 := by
  simp [cnt_varrho_singleton, hx]

private lemma cnt_varrho_zero (N : ℕ) (σ : Fin M → ℝ) :
    varrho N σ {0} = ENNReal.ofReal (max (1 - massRatio N σ) 0) := by
  simp [cnt_varrho_singleton]

private lemma cnt_massRatio_eq (N : ℕ) (σ : Fin M → ℝ) :
    massRatio N σ = ((Finset.univ.filter fun i => 0 < σ i).card : ℝ) / N := rfl

/-- Lemma A.1, general rank: `N ϱ({0}) = (N - rank Σ)₊`. -/
theorem varrho_singleton_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) :
    (N : ℝ) * (varrho N σ {0}).toReal =
      max ((N : ℝ) - (Finset.univ.filter fun i => 0 < σ i).card) 0 := by
  have _ := hσ
  rw [cnt_varrho_zero, ENNReal.toReal_ofReal (le_max_right _ _),
    mul_max_of_nonneg _ _ (Nat.cast_nonneg N), mul_zero, cnt_massRatio_eq]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  congr 1
  field_simp

private lemma cnt_continuousOn_mExt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (fun x : ℝ => mExt N σ x) (Set.Ioi 0) :=
  (continuousOn_mExt N σ hσ).comp Complex.continuous_ofReal.continuousOn
    (fun x hx => Or.inr ⟨Complex.ofReal_im x, Complex.ofReal_ne_zero.mpr (ne_of_gt hx)⟩)

private lemma cnt_continuousOn_rhoDens (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    ContinuousOn (rhoDens N σ) (Set.Ioi 0) :=
  (Complex.continuous_im.comp_continuousOn (cnt_continuousOn_mExt N σ hσ)).div_const _

/-- `ϱ([a, b]) = ∫_a^b ρ` for `0 < a`. -/
private lemma cnt_varrho_Icc (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {a b : ℝ}
    (ha : 0 < a) :
    (varrho N σ (Set.Icc a b)).toReal = ∫ x in Set.Icc a b, rhoDens N σ x := by
  have h0 : (0 : ℝ) ∉ Set.Icc a b := fun h => (not_le.mpr ha) h.1
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.mpr hsub]
  rw [integral_eq_lintegral_of_nonneg_ae]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact div_nonneg (im_mExt_nonneg N σ hσ (ne_of_gt (hsub hx))) Real.pi_pos.le
  · exact ((cnt_continuousOn_rhoDens N σ hσ).mono hsub).aestronglyMeasurable measurableSet_Icc

/-- `ϱ((0, ∞)) = min(1, R)`. -/
private lemma cnt_varrho_Ioi (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    (varrho N σ (Set.Ioi 0)).toReal = min 1 (massRatio N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hIio : varrho N σ (Set.Iio 0) = 0 :=
    measure_mono_null (t := (Set.Icc 0 (edgeVal N σ 1))ᶜ)
      (fun x hx h => (not_le.mpr (Set.mem_Iio.mp hx)) (Set.mem_Icc.mp h).1)
      (varrho_compl_Icc_edgeVal N σ hσ hN hS)
  have hIic : varrho N σ (Set.Iic 0) = varrho N σ {0} := by
    refine le_antisymm ?_ (measure_mono (by simp))
    calc varrho N σ (Set.Iic 0) = varrho N σ (Set.Iio 0 ∪ {0}) := by rw [Set.Iio_union_right]
      _ ≤ varrho N σ (Set.Iio 0) + varrho N σ {0} := measure_union_le _ _
      _ = varrho N σ {0} := by rw [hIio, zero_add]
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    cnt_varrho_zero, ENNReal.toReal_ofReal (le_max_right _ _)]
  rcases le_total (massRatio N σ) 1 with h | h
  · rw [max_eq_left (by linarith), min_eq_right h]; ring
  · rw [max_eq_right (by linarith), min_eq_left h]; ring

/-! ## The critical values `a_k` -/

private lemma cnt_pos_of_mem (σ : Fin M → ℝ) {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma cnt_weight_pos (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight N σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

/-- `a_l ≤ a_k` for `1 ≤ k ≤ l ≤ 2p`. -/
private lemma cnt_edgeVal_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 2 * numBands N σ) : edgeVal N σ j ≤ edgeVal N σ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (edgeVal_succ_le N σ hσ hN hS (by omega) (by omega)).trans (ih (by omega))

/-- `a_{2p} = F(y_{2p}) = y_{2p}² Σ_s r_s s (y_{2p} + s)⁻²`, using `F'(y_{2p}) = 0`. -/
private lemma cnt_edgeVal_last (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    edgeVal N σ (2 * numBands N σ) = ∑ s ∈ posVals σ,
      weight N σ s * s * yEdge N σ ^ 2 / (yEdge N σ + s) ^ 2 := by
  obtain ⟨hin, h1⟩ := yEdge_spec N σ hσ hN hS
  have he : edgeVal N σ (2 * numBands N σ) =
      FChart N σ (yEdge N σ) - yEdge N σ * FChart1 N σ (yEdge N σ) := by
    rw [h1, mul_zero, sub_zero]
    simp [edgeVal]
  rw [he]
  unfold FChart FChart1
  have hterm : ∀ s ∈ posVals σ, weight N σ s * s * yEdge N σ / (yEdge N σ + s) -
      yEdge N σ * (weight N σ s * s ^ 2 / (yEdge N σ + s) ^ 2) =
      weight N σ s * s * yEdge N σ ^ 2 / (yEdge N σ + s) ^ 2 := by
    intro s hs
    have hys : yEdge N σ + s ≠ 0 := (hin s hs).ne'
    field_simp
    ring
  rw [← Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
  ring

private lemma cnt_edgeVal_last_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hN : 0 < N) (hS : (posVals σ).Nonempty) : 0 ≤ edgeVal N σ (2 * numBands N σ) := by
  rw [cnt_edgeVal_last N σ hσ hN hS]
  refine Finset.sum_nonneg fun s hs => ?_
  have := cnt_weight_pos N σ hN hs
  have := cnt_pos_of_mem σ hs
  positivity

private lemma cnt_edgeVal_last_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hN : 0 < N) (hS : (posVals σ).Nonempty) (hy : yEdge N σ ≠ 0) :
    0 < edgeVal N σ (2 * numBands N σ) := by
  rw [cnt_edgeVal_last N σ hσ hN hS]
  refine Finset.sum_pos (fun s hs => ?_) hS
  have := cnt_weight_pos N σ hN hs
  have := cnt_pos_of_mem σ hs
  have hys : 0 < yEdge N σ + s := (yEdge_spec N σ hσ hN hS).1 s hs
  positivity

private lemma cnt_edgeVal_nonneg (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 2 * numBands N σ) :
    0 ≤ edgeVal N σ j :=
  (cnt_edgeVal_last_nonneg N σ hσ hN hS).trans (cnt_edgeVal_anti N σ hσ hN hS hj1 hj le_rfl)

/-- `a_j > 0` for `1 ≤ j < 2p`. -/
private lemma cnt_edgeVal_pos (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {j : ℕ} (hj1 : 1 ≤ j) (hj : j < 2 * numBands N σ) :
    0 < edgeVal N σ j := by
  have hp := (card_innerCrit N σ hσ hN hS).2
  have hlt := edgeVal_band_lt N σ hσ hN hS (k := numBands N σ) hp le_rfl
  have hle := cnt_edgeVal_anti N σ hσ hN hS (i := j) (j := 2 * numBands N σ - 1) hj1 (by omega)
    (by omega)
  linarith [cnt_edgeVal_last_nonneg N σ hσ hN hS]

/-- Lemma A.1, general rank form of (Ni_sum): `Σ_k N_k = N ∧ rank Σ`. -/
theorem sum_bandCount (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) :
    ∑ k ∈ Finset.Icc 1 (numBands N σ), bandCount N σ k =
      min (N : ℝ) (Finset.univ.filter fun i => 0 < σ i).card := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  set p := numBands N σ with hp_def
  set B : ℕ → Set ℝ := fun k => Set.Icc (edgeVal N σ (2 * k)) (edgeVal N σ (2 * k - 1))
    with hB
  have h1 : ∑ k ∈ Finset.Icc 1 p, bandCount N σ k =
      N * (∑ k ∈ Finset.Icc 1 p, varrho N σ (B k)).toReal := by
    rw [ENNReal.toReal_sum (fun k _ => measure_ne_top _ _), Finset.mul_sum]
    rfl
  have key : ∀ k j, 1 ≤ k → k < j → j ≤ p → AEDisjoint (varrho N σ) (B k) (B j) := by
    intro k j hk hkj hj
    refine measure_mono_null (t := {edgeVal N σ (2 * k)}) ?_
      (cnt_varrho_singleton_pos N σ (cnt_edgeVal_pos N σ hσ hN hS (j := 2 * k) (by omega)
        (by omega)).ne')
    rintro x ⟨hx1, hx2⟩
    have := cnt_edgeVal_anti N σ hσ hN hS (i := 2 * k) (j := 2 * j - 1) (by omega) (by omega)
      (by omega)
    exact le_antisymm (hx2.2.trans this) hx1.1
  have hdisj :
      (↑(Finset.Icc 1 p) : Set ℕ).Pairwise (Function.onFun (AEDisjoint (varrho N σ)) B) := by
    intro k hk j hj hkj
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk hj
    rcases lt_or_gt_of_ne hkj with h | h
    · exact key k j hk.1 h hj.2
    · exact (key j k hj.1 h hk.2).symm
  have h2 : ∑ k ∈ Finset.Icc 1 p, varrho N σ (B k) = varrho N σ (⋃ k ∈ Finset.Icc 1 p, B k) :=
    (measure_biUnion_finset₀ hdisj (fun k _ => measurableSet_Icc.nullMeasurableSet)).symm
  have h3 : varrho N σ (⋃ k ∈ Finset.Icc 1 p, B k) = varrho N σ (Set.Ioi 0) := by
    apply measure_congr
    rw [ae_eq_set]
    constructor
    · by_cases hy : yEdge N σ = 0
      · have hR := (yEdge_eq_zero_iff N σ hσ hN hS).mp hy
        refine measure_mono_null (t := {0}) ?_ (by rw [cnt_varrho_singleton]; simp [hR])
        rintro x ⟨hxU, hx⟩
        simp only [Set.mem_iUnion, exists_prop, Finset.mem_Icc] at hxU
        obtain ⟨k, hk, hxk⟩ := hxU
        have := cnt_edgeVal_nonneg N σ hσ hN hS (j := 2 * k) (by omega) (by omega)
        simp only [Set.mem_Ioi, not_lt] at hx
        exact le_antisymm hx (this.trans hxk.1)
      · refine measure_mono_null ?_ measure_empty
        rintro x ⟨hxU, hx⟩
        simp only [Set.mem_iUnion, exists_prop, Finset.mem_Icc] at hxU
        obtain ⟨k, hk, hxk⟩ := hxU
        have hpos : 0 < edgeVal N σ (2 * k) := by
          rcases lt_or_eq_of_le hk.2 with h | h
          · exact cnt_edgeVal_pos N σ hσ hN hS (by omega) (by omega)
          · rw [h]; exact cnt_edgeVal_last_pos N σ hσ hN hS hy
        exact hx (lt_of_lt_of_le hpos hxk.1)
    · refine measure_mono_null ?_ (Measure.measure_compl_support (μ := varrho N σ))
      rintro x ⟨hx, hxU⟩ hsupp
      rw [mem_support_varrho_iff N σ hσ hN hS hx] at hsupp
      obtain ⟨k, hk1, hk, hxk⟩ := hsupp
      exact hxU (Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hk1, hk⟩) hxk)
  rw [h1, h2, h3, cnt_varrho_Ioi N σ hσ hN hS, cnt_massRatio_eq,
    mul_min_of_nonneg _ _ (Nat.cast_nonneg N), mul_one]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  congr 1
  field_simp

/-! ## The critical points `x_k`, `k < 2p` -/

private lemma cnt_nonpole_all (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (by simp [posVals, hpos])

private lemma cnt_critPoly_ne_zero (N : ℕ) (σ : Fin M → ℝ) : critPoly N σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero N σ
  rw [h] at this
  simp at this

/-- `Q(-1/u) ≠ 0` at the poles. -/
private lemma cnt_critPoly_pole (N : ℕ) (σ : Fin M → ℝ) (hN : 0 < N) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly N σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := cnt_pos_of_mem σ hu
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
    (mul_ne_zero (mul_ne_zero (cnt_weight_pos N σ hN hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

/-- For `1 ≤ k < 2p`, `x_k` is the `k`-th entry of the decreasing list of `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)`. -/
private lemma cnt_xCrit_getElem (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    ∃ h : k - 1 < ((innerCrit N σ).sort (· ≤ ·)).reverse.length,
      xCrit N σ k = ((innerCrit N σ).sort (· ≤ ·)).reverse[k - 1] := by
  have hc := (card_innerCrit N σ hσ hN hS).1
  have hlen : ((innerCrit N σ).sort (· ≤ ·)).reverse.length = Multiset.card (innerCrit N σ) := by
    rw [List.length_reverse, Multiset.length_sort]
  have hi : k - 1 < ((innerCrit N σ).sort (· ≤ ·)).reverse.length := by omega
  refine ⟨hi, ?_⟩
  unfold xCrit
  rw [ite_eq_right (by omega)]
  exact List.getD_eq_getElem _ _ hi

private lemma cnt_xCrit_mem (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k ∈ innerCrit N σ := by
  obtain ⟨hi, hx⟩ := cnt_xCrit_getElem N σ hσ hN hS hk1 hk
  rw [hx]
  have := List.getElem_mem hi
  rwa [List.mem_reverse, Multiset.mem_sort] at this

/-- `x_{k+1} ≤ x_k` for `1 ≤ k`, `k + 1 < 2p`. -/
private lemma cnt_xCrit_anti (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 < 2 * numBands N σ) :
    xCrit N σ (k + 1) ≤ xCrit N σ k := by
  obtain ⟨hi, hx⟩ := cnt_xCrit_getElem N σ hσ hN hS hk1 (by omega)
  obtain ⟨hi', hx'⟩ := cnt_xCrit_getElem N σ hσ hN hS (k := k + 1) (by omega) hk
  rw [hx, hx']
  have hpw : ((innerCrit N σ).sort (· ≤ ·)).reverse.Pairwise (fun a b => b ≤ a) :=
    List.pairwise_reverse.2 (Multiset.pairwise_sort _ _)
  exact List.pairwise_iff_getElem.mp hpw (k - 1) (k + 1 - 1) hi hi' (by omega)

/-- For `1 ≤ k < 2p`: `x_k < 0` and `x_k` is not a pole. -/
private lemma cnt_xCrit_good (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands N σ) :
    xCrit N σ k < 0 ∧ ∀ i, 1 + σ i * xCrit N σ k ≠ 0 := by
  have hm := cnt_xCrit_mem N σ hσ hN hS hk1 hk
  unfold innerCrit at hm
  rw [Multiset.mem_filter, mem_roots (cnt_critPoly_ne_zero N σ)] at hm
  obtain ⟨hroot, hin⟩ := hm
  have h0 : (critPoly N σ).eval (xCrit N σ k) = 0 := hroot
  refine ⟨hin.1, cnt_nonpole_all σ hσ fun u hu h => ?_⟩
  have hu0 := cnt_pos_of_mem σ hu
  have hx' : xCrit N σ k = -u⁻¹ := by
    field_simp
    linear_combination h
  rw [hx'] at h0
  exact cnt_critPoly_pole N σ hN hu h0

/-! ## The primitive `Φ(w) = w f(w) + log w - N⁻¹ Σ_{σ_i > 0} log(w + σ_i⁻¹)` -/

private def cntPhi (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) : ℂ :=
  w * fC N σ w + Complex.log w -
    ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i),
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Complex.log (w + (((σ i)⁻¹ : ℝ) : ℂ))

private lemma cnt_nonpole_of_im (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {w : ℂ} (hw : 0 < w.im) :
    ∀ i, 1 + (σ i : ℂ) * w ≠ 0 := by
  intro i h
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0] at h; simp at h
  · have h2 : σ i * w.im = 0 := by simpa using congrArg Complex.im h
    exact (mul_pos hpos hw).ne' h2

/-- `f(w) = -w⁻¹ + N⁻¹ Σ_{σ_i > 0} (w + σ_i⁻¹)⁻¹` off the poles. -/
private lemma cnt_fC_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {w : ℂ}
    (hw' : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    fC N σ w = -w⁻¹ + ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i),
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * (w + (((σ i)⁻¹ : ℝ) : ℂ))⁻¹ := by
  unfold fC
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have hσi : (σ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have h1 := hw' i
    have h2 : w + (((σ i)⁻¹ : ℝ) : ℂ) = (1 + σ i * w) / σ i := by
      push_cast
      field_simp
      ring
    rw [h2]
    push_cast
    field_simp
  · have : σ i = 0 := le_antisymm (not_lt.mp h) (hσ i)
    simp [this]

private lemma cnt_hasDerivAt_Phi (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {w : ℂ} (hw : 0 < w.im) : HasDerivAt (cntPhi N σ) (w * fCDeriv N σ w) w := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hw' := cnt_nonpole_of_im σ hσ hw
  have hslit : ∀ c : ℝ, w + (c : ℂ) ∈ Complex.slitPlane := fun c =>
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hw.ne'))
  have d1 := (hasDerivAt_id w).mul (hasDerivAt_fC N σ hw0 hw')
  have d2 := Complex.hasDerivAt_log (by simpa using hslit 0)
  have d3 := HasDerivAt.fun_sum (u := Finset.univ.filter (fun i => 0 < σ i))
    (A := fun i z => (((N : ℝ)⁻¹ : ℝ) : ℂ) * Complex.log (z + (((σ i)⁻¹ : ℝ) : ℂ)))
    (fun i _ => (((hasDerivAt_id w).add_const _).clog (hslit _)).const_mul _)
  have := (d1.add d2).sub d3
  convert this using 1
  · funext z; rfl
  rw [cnt_fC_eq N σ hσ hN hw']
  simp only [id, one_div, one_mul]
  ring

private lemma cnt_cwa_log_shift {w : ℂ} (c : ℝ) (h : 0 < w.im ∨ (w.im = 0 ∧ w.re + c ≠ 0)) :
    ContinuousWithinAt (fun z : ℂ => Complex.log (z + c)) {z | 0 ≤ z.im} w := by
  by_cases hs : w + c ∈ Complex.slitPlane
  · exact ((continuousAt_clog hs).comp (f := fun z : ℂ => z + (c : ℂ))
      (continuous_id.add continuous_const).continuousAt).continuousWithinAt
  · rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hs
    have him : (w + c).im = 0 := hs.2
    have hre : (w + c).re < 0 := by
      rcases h with h | h
      · simp at him; linarith
      · simp only [Complex.add_re, Complex.ofReal_re] at hs ⊢
        exact lt_of_le_of_ne hs.1 h.2
    exact (Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre him).comp
      (f := fun z : ℂ => z + (c : ℂ)) (continuous_id.add continuous_const).continuousWithinAt
      (fun z hz => by simpa using hz)

private lemma cnt_cwa_Phi_upper (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {w : ℂ} (hw : 0 < w.im) : ContinuousWithinAt (cntPhi N σ) {z | 0 ≤ z.im} w :=
  (cnt_hasDerivAt_Phi N σ hσ hN hw).continuousAt.continuousWithinAt

private lemma cnt_cwa_Phi_real (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x < 0)
    (hnp : ∀ i, 1 + σ i * x ≠ 0) : ContinuousWithinAt (cntPhi N σ) {z | 0 ≤ z.im} x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne
  have hnp' : ∀ i, 1 + (σ i : ℂ) * x ≠ 0 := fun i => by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (hnp i)
  have h1 : ContinuousWithinAt (fun z => z * fC N σ z) {z | 0 ≤ z.im} x :=
    (continuousAt_id.mul (hasDerivAt_fC N σ hx0 hnp').continuousAt).continuousWithinAt
  have h2 : ContinuousWithinAt Complex.log {z | 0 ≤ z.im} x :=
    Complex.continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hx) (by simp)
  have h3 : ContinuousWithinAt (fun z => ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i),
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Complex.log (z + (((σ i)⁻¹ : ℝ) : ℂ))) {z | 0 ≤ z.im} x := by
    refine tendsto_finsetSum _ fun i hi => (continuousWithinAt_const.mul ?_ :
      ContinuousWithinAt (fun z : ℂ => (((N : ℝ)⁻¹ : ℝ) : ℂ) *
        Complex.log (z + (((σ i)⁻¹ : ℝ) : ℂ))) {z | 0 ≤ z.im} x)
    refine cnt_cwa_log_shift _ (Or.inr ⟨by simp, ?_⟩)
    have hσi : σ i ≠ 0 := (Finset.mem_filter.mp hi).2.ne'
    intro h
    apply hnp i
    simp only [Complex.ofReal_re] at h
    have : 1 + σ i * x = σ i * (x + (σ i)⁻¹) := by field_simp; ring
    rw [this, h, mul_zero]
  exact (h1.add h2).sub h3

/-- `Im Φ(x) = π - N⁻¹ Σ_{σ_i > 0} π 1[x + σ_i⁻¹ < 0]` for real `x < 0`. -/
private lemma cnt_im_Phi_real (N : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : x < 0) :
    (cntPhi N σ x).im = Real.pi - ∑ i ∈ Finset.univ.filter (fun i => 0 < σ i),
      (N : ℝ)⁻¹ * (Real.pi * if x + (σ i)⁻¹ < 0 then 1 else 0) := by
  have h1 : ((x : ℂ) * (fR N σ x : ℂ)).im = 0 := by
    rw [← Complex.ofReal_mul]; exact Complex.ofReal_im _
  have h2 : (Complex.log x).im = Real.pi := by
    rw [Complex.log_im, Complex.arg_ofReal_of_neg hx]
  have h3 : ∀ i ∈ Finset.univ.filter (fun i => 0 < σ i),
      ((((N : ℝ)⁻¹ : ℝ) : ℂ) * Complex.log (x + (((σ i)⁻¹ : ℝ) : ℂ))).im =
        (N : ℝ)⁻¹ * (Real.pi * if x + (σ i)⁻¹ < 0 then 1 else 0) := by
    intro i _
    rw [Complex.im_ofReal_mul, ← Complex.ofReal_add, Complex.log_im]
    split_ifs with h
    · rw [Complex.arg_ofReal_of_neg h, mul_one]
    · rw [Complex.arg_ofReal_of_nonneg (not_lt.mp h)]; simp
  rw [cntPhi, fC_ofReal, Complex.sub_im, Complex.add_im, h1, h2, Complex.im_sum,
    Finset.sum_congr rfl h3, zero_add]

/-! ## `m` near a point of an open band -/

private lemma cnt_fC_mExt (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ} (hE : 0 < E)
    (him : 0 < (mExt N σ E).im) : fC N σ (mExt N σ E) = E := by
  have hw0 : mExt N σ E ≠ 0 := fun h => by rw [h] at him; simp at him
  have hnp : ∀ s ∈ posVals σ, 1 + (s : ℂ) * mExt N σ E ≠ 0 := fun s hs h => by
    have h2 : s * (mExt N σ E).im = 0 := by simpa using congrArg Complex.im h
    exact (mul_pos (cnt_pos_of_mem σ hs) him).ne' h2
  have h0 := scPoly_eval_mExt N σ hσ hE.ne'
  rw [scPoly_eval N σ hσ _ hw0 hnp] at h0
  have hprod : ∏ s ∈ posVals σ, (1 + (s : ℂ) * mExt N σ E) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hnp
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero hw0 hprod))

/-- On an open band, `E ↦ Φ(m(E))` has derivative `m(E)`: there `m` is the holomorphic local
inverse of `f` at `m(E) ∈ ℂ₊`, and `Φ'(w) = w f'(w)`. -/
private lemma cnt_hasDerivAt_Psi (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    {E : ℝ} (hE : 0 < E) (him : 0 < (mExt N σ E).im) :
    HasDerivAt (fun x : ℝ => cntPhi N σ (mExt N σ x)) (mExt N σ E) E := by
  set w0 := mExt N σ (E : ℂ) with hw0def
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hne0 : ∀ {w : ℂ}, 0 < w.im → w ≠ 0 := fun hw h => by rw [h] at hw; simp at hw
  have hdiff : DifferentiableOn ℂ (fC N σ) upperHalf := fun w hw =>
    (hasDerivAt_fC N σ (hne0 hw)
      (cnt_nonpole_of_im σ hσ hw)).differentiableAt.differentiableWithinAt
  have hd : HasDerivAt (fC N σ) (fCDeriv N σ w0) w0 :=
    hasDerivAt_fC N σ (hne0 him) (cnt_nonpole_of_im σ hσ him)
  have hs : HasStrictDerivAt (fC N σ) (fCDeriv N σ w0) w0 := by
    have := (hdiff.analyticAt (hopen.mem_nhds him)).hasStrictDerivAt
    rwa [hd.deriv] at this
  have hfE : fC N σ w0 = E := cnt_fC_mExt N σ hσ hE him
  have hne : fCDeriv N σ w0 ≠ 0 := fCDeriv_ne_zero N σ hσ him (by rw [hfE]; simp)
  have hleft := hs.eventually_left_inverse hne
  have hg : HasDerivAt (hs.localInverse (fC N σ) (fCDeriv N σ w0) w0 hne)
      (fCDeriv N σ w0)⁻¹ E := by
    have := (hs.to_localInverse hne).hasDerivAt
    rwa [hfE] at this
  have hgE : hs.localInverse (fC N σ) (fCDeriv N σ w0) w0 hne E = w0 := by
    have := hleft.self_of_nhds
    rwa [hfE] at this
  have hcont : ContinuousAt (fun x : ℝ => mExt N σ x) E :=
    (cnt_continuousOn_mExt N σ hσ).continuousAt (Ioi_mem_nhds hE)
  have hev : ∀ᶠ x : ℝ in 𝓝 E,
      mExt N σ x = hs.localInverse (fC N σ) (fCDeriv N σ w0) w0 hne x := by
    have h1 := hcont.eventually_mem (inter_mem hleft (hopen.mem_nhds him))
    filter_upwards [h1, Ioi_mem_nhds hE] with x hx hxpos
    have h2 := hx.1
    simp only [Set.mem_ofPred_eq] at h2
    rw [cnt_fC_mExt N σ hσ hxpos hx.2] at h2
    exact h2.symm
  have hPhi : HasDerivAt (cntPhi N σ) (w0 * fCDeriv N σ w0)
      (hs.localInverse (fC N σ) (fCDeriv N σ w0) w0 hne E) := by
    rw [hgE]; exact cnt_hasDerivAt_Phi N σ hσ hN him
  have hcomp := (hPhi.comp (E : ℂ) hg).comp_ofReal
  rw [mul_assoc, mul_inv_cancel₀ hne, mul_one] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hev] with x hx
  simp only [Function.comp, hx]

/-! ## (Ni_rep) -/

private lemma cnt_ind (xa xb t : ℝ) (hab : xa ≤ xb) (hne : xa + t ≠ 0) :
    ((if xa + t < 0 then (1 : ℝ) else 0) - (if xb + t < 0 then 1 else 0)) =
      if xa ≤ -t ∧ -t ≤ xb then 1 else 0 := by
  by_cases hA : xa + t < 0
  · by_cases hB : xb + t < 0
    · rw [ite_eq_left hA, ite_eq_left hB, ite_eq_right (fun h => by linarith [h.2])]
      ring
    · rw [ite_eq_left hA, ite_eq_right hB, ite_eq_left ⟨by linarith, by linarith⟩]
      ring
  · have hB : ¬ xb + t < 0 := fun h => hA (by linarith)
    have hA' : 0 < xa + t := lt_of_le_of_ne (not_lt.mp hA) (Ne.symm hne)
    rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right (fun h => by linarith [h.1])]
    ring

/-- Lemma A.1, (Ni_rep), `k = 1, …, p - 1`. -/
theorem bandCount_eq_card (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k < numBands N σ) :
    bandCount N σ k = (Finset.univ.filter fun j =>
      xCrit N σ (2 * k) ≤ -(σ j)⁻¹ ∧ -(σ j)⁻¹ ≤ xCrit N σ (2 * k - 1)).card := by
  set a := edgeVal N σ (2 * k) with ha_def
  set b := edgeVal N σ (2 * k - 1) with hb_def
  set xa := xCrit N σ (2 * k) with hxa_def
  set xb := xCrit N σ (2 * k - 1) with hxb_def
  set P := Finset.univ.filter (fun i => 0 < σ i) with hP
  have ha : 0 < a := cnt_edgeVal_pos N σ hσ hN hS (by omega) (by omega)
  have hab : a < b := edgeVal_band_lt N σ hσ hN hS hk₁ hk.le
  have hma : mExt N σ a = xa :=
    mExt_edgeVal N σ hσ hN hS (by omega) (by omega) (fun h => by omega)
  have hmb : mExt N σ b = xb :=
    mExt_edgeVal N σ hσ hN hS (k := 2 * k - 1) (by omega) (by omega) (fun h => by omega)
  obtain ⟨hxa0, hxanp⟩ := cnt_xCrit_good N σ hσ hN hS (k := 2 * k) (by omega) (by omega)
  obtain ⟨hxb0, hxbnp⟩ := cnt_xCrit_good N σ hσ hN hS (k := 2 * k - 1) (by omega) (by omega)
  have hxab : xa ≤ xb := by
    have := cnt_xCrit_anti N σ hσ hN hS (k := 2 * k - 1) (by omega) (by omega)
    rwa [show 2 * k - 1 + 1 = 2 * k by omega] at this
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have him : ∀ x ∈ Set.Ioo a b, 0 < (mExt N σ x).im := fun x hx => by
    have := rhoDens_pos N σ hσ hN hS hk₁ hk.le (lt_trans ha hx.1) hx
    unfold rhoDens at this
    exact (div_pos_iff_of_pos_right Real.pi_pos).mp this
  have hcont : ContinuousOn (fun x : ℝ => cntPhi N σ (mExt N σ x)) (Set.Icc a b) := by
    intro x hx
    have hmx : ContinuousWithinAt (fun x : ℝ => mExt N σ x) (Set.Icc a b) x :=
      ((cnt_continuousOn_mExt N σ hσ).mono hsub) x hx
    have hmaps : Set.MapsTo (fun x : ℝ => mExt N σ x) (Set.Icc a b) {z | 0 ≤ z.im} :=
      fun y hy => im_mExt_nonneg N σ hσ (hsub hy).ne'
    refine ContinuousWithinAt.comp (g := cntPhi N σ) (t := {z : ℂ | 0 ≤ z.im}) ?_ hmx hmaps
    show ContinuousWithinAt (cntPhi N σ) {z : ℂ | 0 ≤ z.im} (mExt N σ x)
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h, hma]; exact cnt_cwa_Phi_real N σ hxa0 hxanp
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · rw [h', hmb]; exact cnt_cwa_Phi_real N σ hxb0 hxbnp
    exact cnt_cwa_Phi_upper N σ hσ hN (him x ⟨h, h'⟩)
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun x : ℝ => cntPhi N σ (mExt N σ x)) (mExt N σ x) x :=
    fun x hx => cnt_hasDerivAt_Psi N σ hσ hN (lt_trans ha hx.1) (him x hx)
  have hint : IntervalIntegrable (fun x : ℝ => mExt N σ x) volume a b :=
    ((cnt_continuousOn_mExt N σ hσ).mono
      (by rw [Set.uIcc_of_le hab.le]; exact hsub)).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcont hderiv hint
  simp only [hma, hmb] at hftc
  have hrho : ∫ x in a..b, rhoDens N σ x = (∫ x in a..b, mExt N σ x).im / Real.pi := by
    have := intervalIntegral.intervalIntegral_im hint
    simp only [RCLike.im_to_complex] at this
    unfold rhoDens
    rw [intervalIntegral.integral_div, this]
  have hterm : ∀ i ∈ P, (N : ℝ)⁻¹ * (Real.pi * if xa + (σ i)⁻¹ < 0 then 1 else 0) -
      (N : ℝ)⁻¹ * (Real.pi * if xb + (σ i)⁻¹ < 0 then 1 else 0) =
      (N : ℝ)⁻¹ * Real.pi * if xa ≤ -(σ i)⁻¹ ∧ -(σ i)⁻¹ ≤ xb then 1 else 0 := by
    intro i hi
    have hσi : σ i ≠ 0 := (Finset.mem_filter.mp hi).2.ne'
    have hne : xa + (σ i)⁻¹ ≠ 0 := by
      intro h
      apply hxanp i
      have : 1 + σ i * xa = σ i * (xa + (σ i)⁻¹) := by field_simp; ring
      rw [this, h, mul_zero]
    rw [← cnt_ind xa xb _ hxab hne]
    ring
  have hfilt : (P.filter fun j => xa ≤ -(σ j)⁻¹ ∧ -(σ j)⁻¹ ≤ xb) =
      Finset.univ.filter fun j => xa ≤ -(σ j)⁻¹ ∧ -(σ j)⁻¹ ≤ xb := by
    rw [hP, Finset.filter_filter]
    refine Finset.filter_congr fun j _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rcases (hσ j).eq_or_lt with h0 | hpos
    · exfalso
      rw [← h0, inv_zero, neg_zero] at h
      linarith [h.2]
    · exact hpos
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [bandCount, cnt_varrho_Icc N σ hσ ha, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, hrho, hftc, Complex.sub_im,
    cnt_im_Phi_real N σ hxb0, cnt_im_Phi_real N σ hxa0, ← hfilt, ← Finset.sum_boole,
    show ∀ A B : ℝ, Real.pi - A - (Real.pi - B) = B - A from fun A B => by ring,
    ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  field_simp

theorem bandCount_eq_natCast (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ numBands N σ) :
    ∃ n : ℕ, bandCount N σ k = n := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact ⟨_, bandCount_eq_card N σ hσ hN hS hk₁ hlt⟩
  have hsum := sum_bandCount N σ hσ hN hS
  obtain ⟨q, hq⟩ : ∃ q, numBands N σ = q + 1 := ⟨numBands N σ - 1, by omega⟩
  rw [hq, Finset.sum_Icc_succ_top (by omega)] at hsum
  have hcard : ∀ j ∈ Finset.Icc 1 q, bandCount N σ j = ((Finset.univ.filter fun i =>
      xCrit N σ (2 * j) ≤ -(σ i)⁻¹ ∧ -(σ i)⁻¹ ≤ xCrit N σ (2 * j - 1)).card : ℝ) :=
    fun j hj => bandCount_eq_card N σ hσ hN hS (Finset.mem_Icc.mp hj).1
      (by rw [hq]; have := (Finset.mem_Icc.mp hj).2; omega)
  rw [Finset.sum_congr rfl hcard, ← Nat.cast_sum, ← Nat.cast_min] at hsum
  set S := ∑ j ∈ Finset.Icc 1 q, (Finset.univ.filter fun i =>
      xCrit N σ (2 * j) ≤ -(σ i)⁻¹ ∧ -(σ i)⁻¹ ≤ xCrit N σ (2 * j - 1)).card
  set T := min N (Finset.univ.filter fun i => 0 < σ i).card
  have hnn : 0 ≤ bandCount N σ (q + 1) := by unfold bandCount; positivity
  have hle : S ≤ T := by
    have : (S : ℝ) ≤ T := by linarith
    exact_mod_cast this
  refine ⟨T - S, ?_⟩
  rw [heq, hq, Nat.cast_sub hle]
  linarith

/-- Lemma A.1 as stated (`σ_j > 0` for all `j`): `N ϱ({0}) = (N - M)₊` and (Ni_sum). -/
theorem Ni_sum (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ j, 0 < σ j) (hN : 0 < N) (hM : 0 < M) :
    (N : ℝ) * (varrho N σ {0}).toReal = max ((N : ℝ) - M) 0 ∧
      ∑ k ∈ Finset.Icc 1 (numBands N σ), bandCount N σ k = min (N : ℝ) M := by
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le
  have hfilt : (Finset.univ.filter fun i => 0 < σ i) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hσ i
  have hS : (posVals σ).Nonempty :=
    ⟨σ ⟨0, hM⟩, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hσ _⟩⟩
  have h1 := varrho_singleton_zero N σ hσ' hN
  have h2 := sum_bandCount N σ hσ' hN hS
  rw [hfilt, Finset.card_univ, Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Definition 2.7 (regularity) -/

/-! ## Instances

Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1` (`φ = 1/2`, `p = 1`, `x_1 = √2 - 2`,
`a_1 = 3/2 + √2`, `a_2 = 3/2 - √2`). Two components: `M = 2`, `N = 20`, `σ = (10, 1)`, with
three critical points in `I_1 ∪ I_2`, so `p = 2`. -/

/-- Lemma A.1, the atom, at Marchenko–Pastur. -/
example : (2 : ℝ) * (varrho 2 (fun _ : Fin 1 => (1 : ℝ)) {0}).toReal =
    max ((2 : ℝ) - (Finset.univ.filter fun i : Fin 1 => 0 < (fun _ : Fin 1 => (1 : ℝ)) i).card)
      0 :=
  varrho_singleton_zero 2 (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num) (by norm_num)

example : (2 : ℝ) * (varrho 2 (fun _ : Fin 1 => (1 : ℝ)) {0}).toReal = 1 := by
  have h := varrho_singleton_zero 2 (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num)
    (by norm_num)
  push_cast at h
  rw [h]
  norm_num

/-- (Ni_sum), general rank, at Marchenko–Pastur. -/
example : ∑ k ∈ Finset.Icc 1 (numBands 2 (fun _ : Fin 1 => (1 : ℝ))),
      bandCount 2 (fun _ : Fin 1 => (1 : ℝ)) k =
    min (2 : ℝ) (Finset.univ.filter fun i : Fin 1 => 0 < (fun _ : Fin 1 => (1 : ℝ)) i).card :=
  sum_bandCount 2 (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num) (by norm_num)
    ⟨1, by simp [posVals]⟩

/-- Lemma A.1 as stated at Marchenko–Pastur. -/
example : (2 : ℝ) * (varrho 2 (fun _ : Fin 1 => (1 : ℝ)) {0}).toReal = max ((2 : ℝ) - 1) 0 ∧
    ∑ k ∈ Finset.Icc 1 (numBands 2 (fun _ : Fin 1 => (1 : ℝ))),
      bandCount 2 (fun _ : Fin 1 => (1 : ℝ)) k = min (2 : ℝ) 1 := by
  exact_mod_cast Ni_sum 2 (fun _ : Fin 1 => (1 : ℝ)) (fun _ => by norm_num) (by norm_num)
    (by norm_num)

end Anisotropic
