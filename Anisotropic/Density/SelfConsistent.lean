module

public import Anisotropic.MainDefs
public import Anisotropic.Density.Poly

@[expose] public section

/-!
# The self-consistent equation and its solution `m`

For `σ ≥ 0` and `z ∈ ℂ₊`, the equation `f(m) = z` of (def_m), equivalently (m_sc_eq), has exactly
one solution `m ∈ ℂ₊` (Lemma 2.2 for the empirical measure `π` of (def_pi), Definition 2.3).
This file defines `m = mFun`, and proves (m_sc_eq), the bound `|m(z)| ≤ (1 + √R) / |z|`,
`f'(w) ≠ 0` for `w ∈ ℂ₊` with `Im f(w) ≥ 0`, and that `m` is analytic on `ℂ₊` with
`m'(z) = 1 / f'(m(z))`.

Uniqueness follows from `f(w₁) - f(w₂) = (w₁ - w₂) (1/(w₁ w₂) - N⁻¹ Σ_i σ_i² a_i(w₁) a_i(w₂))`
with `a_i(w) = 1/(1 + σ_i w)` and the Cauchy–Schwarz inequality. Existence follows from the fact
that the set of `z ∈ ℂ₊` attained by `f` on `ℂ₊` is nonempty, open and relatively closed in the
connected set `ℂ₊`.
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Elementary facts on `ℂ₊` -/

private lemma sc_isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const Complex.continuous_im

private lemma sc_ne_zero {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := by
  rintro rfl
  simp at hw

/-- `1 + σ_i w ≠ 0` for `w ∈ ℂ₊`: `f` has no pole in `ℂ₊`. -/
private lemma sc_den_ne_zero (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im) (i : Fin M) :
    1 + (σ i : ℂ) * w ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 := congrArg Complex.re h
  simp at h1 h2
  rcases h1 with h1 | h1
  · rw [h1] at h2
    simp at h2
  · linarith

private lemma sc_hasDerivAt (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fC N σ) (fCDeriv N σ w) w :=
  hasDerivAt_fC N σ (sc_ne_zero hw) (sc_den_ne_zero σ hw)

private lemma sc_hasStrictDerivAt (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasStrictDerivAt (fC N σ) (fCDeriv N σ w) w := by
  have hd : DifferentiableOn ℂ (fC N σ) upperHalf := fun x hx =>
    (sc_hasDerivAt N σ (show 0 < x.im from hx)).differentiableAt.differentiableWithinAt
  have h := (hd.analyticAt (sc_isOpen_upperHalf.mem_nhds hw)).hasStrictDerivAt
  rwa [(sc_hasDerivAt N σ hw).deriv] at h

/-! ## Consequences of `Im f(w) = Im w (|w|⁻² - N⁻¹ Σ_i σ_i² |1 + σ_i w|⁻²)` -/

private lemma sc_A_nonneg (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) :
    0 ≤ ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) :=
  Finset.sum_nonneg fun i _ => by positivity

private lemma sc_A_le (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im)
    (hf : 0 ≤ (fC N σ w).im) :
    ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) ≤ (‖w‖ ^ 2)⁻¹ := by
  rw [im_fC] at hf
  by_contra h
  push Not at h
  have : w.im * ((‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)) < 0 :=
    mul_neg_of_pos_of_neg hw (by linarith)
  linarith

private lemma sc_A_lt (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im)
    (hf : 0 < (fC N σ w).im) :
    ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) < (‖w‖ ^ 2)⁻¹ := by
  rw [im_fC] at hf
  by_contra h
  push Not at h
  have : w.im * ((‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hw.le (by linarith)
  linarith

/-- `Im f(w) |w|² ≤ Im w` on `ℂ₊`. -/
private lemma sc_im_bound (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im) :
    (fC N σ w).im * ‖w‖ ^ 2 ≤ w.im := by
  rw [im_fC]
  have hA := sc_A_nonneg N σ w
  set A := ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (sc_ne_zero hw)
  have h : w.im * ((‖w‖ ^ 2)⁻¹ - A) * ‖w‖ ^ 2 = w.im - w.im * A * ‖w‖ ^ 2 := by
    field_simp
  rw [h]
  have : 0 ≤ w.im * A * ‖w‖ ^ 2 := by positivity
  linarith

/-- A lower bound on `|w|` in terms of `|f(w)|` on `ℂ₊`. -/
private lemma sc_norm_lower (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {w : ℂ}
    (hw : 0 < w.im) : 1 / (2 * (1 + ∑ i, σ i) + ‖fC N σ w‖) ≤ ‖w‖ := by
  set S := ∑ i, σ i with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hσ i
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (sc_ne_zero hw)
  have hD : 0 < 2 * (1 + S) + ‖fC N σ w‖ := by positivity
  by_contra hlt
  push Not at hlt
  have h1 : ‖w‖ * (2 * (1 + S) + ‖fC N σ w‖) < 1 := by rwa [lt_div_iff₀ hD] at hlt
  have hsmall : ∀ i, σ i * ‖w‖ ≤ 1 / 2 := by
    intro i
    have hi : σ i ≤ S := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
    nlinarith [mul_le_mul_of_nonneg_right hi hw0.le, mul_nonneg (norm_nonneg (fC N σ w)) hw0.le]
  have hterm : ∀ i, ‖(σ i : ℂ) / (N * (1 + σ i * w))‖ ≤ 2 * σ i := by
    intro i
    have hB : 1 / 2 ≤ ‖1 + (σ i : ℂ) * w‖ := by
      have e : (1 : ℂ) = (1 + σ i * w) + (-(σ i * w)) := by ring
      have h2 : ‖(1 : ℂ)‖ ≤ ‖1 + (σ i : ℂ) * w‖ + ‖-((σ i : ℂ) * w)‖ := by
        conv_lhs => rw [e]
        exact norm_add_le _ _
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hσ i), norm_one] at h2
      linarith [hsmall i]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hσ i), Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Nat.cast_zero, zero_mul, div_zero]
      linarith [hσ i]
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpos : 0 < (N : ℝ) * ‖1 + (σ i : ℂ) * w‖ := by positivity
      have hNB : 1 / 2 ≤ (N : ℝ) * ‖1 + (σ i : ℂ) * w‖ := by nlinarith
      rw [div_le_iff₀ hpos]
      nlinarith [mul_le_mul_of_nonneg_left hNB (hσ i)]
  have hinv : ‖w‖⁻¹ ≤ 2 * S + ‖fC N σ w‖ := by
    have e : w⁻¹ = (∑ i, (σ i : ℂ) / (N * (1 + σ i * w))) - fC N σ w := by
      unfold fC
      ring
    rw [← norm_inv, e]
    refine (norm_sub_le _ _).trans ?_
    have hs : ‖∑ i, (σ i : ℂ) / (N * (1 + σ i * w))‖ ≤ 2 * S := by
      refine (norm_sum_le _ _).trans ?_
      rw [hSdef, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hterm i
    linarith
  have h3 : 1 ≤ ‖w‖ * (2 * S + ‖fC N σ w‖) := by
    have := mul_le_mul_of_nonneg_left hinv hw0.le
    rwa [mul_inv_cancel₀ hw0.ne'] at this
  nlinarith

/-! ## Uniqueness -/

private lemma sc_diff (N : ℕ) (σ : Fin M → ℝ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    fC N σ w₁ - fC N σ w₂ = (w₁ - w₂) * ((w₁ * w₂)⁻¹ -
      ∑ i, (σ i : ℂ) ^ 2 / (N * (1 + σ i * w₁) * (1 + σ i * w₂))) := by
  have hw1 := sc_ne_zero h₁
  have hw2 := sc_ne_zero h₂
  have hterm : ∀ i, (σ i : ℂ) / (N * (1 + σ i * w₁)) - σ i / (N * (1 + σ i * w₂)) =
      -((w₁ - w₂) * ((σ i : ℂ) ^ 2 / (N * (1 + σ i * w₁) * (1 + σ i * w₂)))) := by
    intro i
    have hb1 := sc_den_ne_zero σ h₁ i
    have hb2 := sc_den_ne_zero σ h₂ i
    by_cases hN : (N : ℂ) = 0
    · simp [hN]
    · field_simp
      ring
  have hsum : ∑ i, (σ i : ℂ) / (N * (1 + σ i * w₁)) - ∑ i, (σ i : ℂ) / (N * (1 + σ i * w₂)) =
      -∑ i, (w₁ - w₂) * ((σ i : ℂ) ^ 2 / (N * (1 + σ i * w₁) * (1 + σ i * w₂))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hinv : -w₁⁻¹ - -w₂⁻¹ = (w₁ - w₂) * (w₁ * w₂)⁻¹ := by
    field_simp
    ring
  unfold fC
  rw [mul_sub, Finset.mul_sum]
  linear_combination hsum + hinv

private lemma sc_unique (N : ℕ) (σ : Fin M → ℝ) {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im)
    (hz : 0 < (fC N σ w₁).im) (h : fC N σ w₁ = fC N σ w₂) : w₁ = w₂ := by
  by_contra hne
  have hz2 : 0 < (fC N σ w₂).im := h ▸ hz
  have hd := sc_diff N σ h₁ h₂
  rw [h, sub_self] at hd
  have hbr : (w₁ * w₂)⁻¹ =
      ∑ i, (σ i : ℂ) ^ 2 / (N * (1 + σ i * w₁) * (1 + σ i * w₂)) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left (sub_ne_zero.mpr hne))
  set r : Fin M → ℝ := fun i =>
    σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w₁‖ * ‖1 + (σ i : ℂ) * w₂‖) with hr
  set g₁ : Fin M → ℝ := fun i => σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w₁‖ ^ 2) with hg₁
  set g₂ : Fin M → ℝ := fun i => σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w₂‖ ^ 2) with hg₂
  have hn : ‖(w₁ * w₂)⁻¹‖ ≤ ∑ i, r i := by
    rw [hbr]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp [hr]
  have hCS : (∑ i, r i) ^ 2 ≤ (∑ i, g₁ i) * ∑ i, g₂ i :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => by positivity)
      (fun i _ => by positivity) (fun i _ => le_of_eq (by simp only [hr, hg₁, hg₂]; ring))
  have hA1 := sc_A_lt N σ h₁ hz
  have hA2 := sc_A_lt N σ h₂ hz2
  have hprod : (∑ i, g₁ i) * (∑ i, g₂ i) < (‖w₁‖ ^ 2)⁻¹ * (‖w₂‖ ^ 2)⁻¹ :=
    mul_lt_mul'' hA1 hA2 (sc_A_nonneg N σ w₁) (sc_A_nonneg N σ w₂)
  have hsq : ‖(w₁ * w₂)⁻¹‖ ^ 2 = (‖w₁‖ ^ 2)⁻¹ * (‖w₂‖ ^ 2)⁻¹ := by
    rw [norm_inv, norm_mul]
    ring
  have hn2 : ‖(w₁ * w₂)⁻¹‖ ^ 2 ≤ (∑ i, r i) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  linarith

/-! ## `f'(w) ≠ 0` -/

/-- `Re (w² f'(w)) > 0` for `w ∈ ℂ₊` with `Im f(w) ≥ 0`. -/
private lemma sc_re_pos (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : 0 < w.im)
    (hf : 0 ≤ (fC N σ w).im) : 0 < (w ^ 2 * fCDeriv N σ w).re := by
  have hw0 := sc_ne_zero hw
  set u : Fin M → ℂ := fun i => w / (1 + σ i * w) with hu
  set c : Fin M → ℝ := fun i => σ i ^ 2 / N with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by simp only [hc]; positivity
  have hid : w ^ 2 * fCDeriv N σ w = 1 - ∑ i, (c i : ℂ) * u i ^ 2 := by
    unfold fCDeriv
    rw [mul_sub, mul_inv_cancel₀ (pow_ne_zero 2 hw0), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hB := sc_den_ne_zero σ hw i
    simp only [hc, hu]
    push_cast
    by_cases hN : (N : ℂ) = 0
    · simp [hN]
    · field_simp
  have hre : ∀ i, ((c i : ℂ) * u i ^ 2).re = c i * ‖u i‖ ^ 2 - 2 * (c i * (u i).im ^ 2) := by
    intro i
    rw [Complex.re_ofReal_mul, Complex.sq_norm, Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  have huim : ∀ i, 0 < (u i).im := by
    intro i
    have hB := sc_den_ne_zero σ hw i
    have hn : 0 < Complex.normSq (1 + (σ i : ℂ) * w) := Complex.normSq_pos.mpr hB
    have e : (w / (1 + (σ i : ℂ) * w)).im = w.im / Complex.normSq (1 + (σ i : ℂ) * w) := by
      rw [Complex.div_im]
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero,
        add_zero, zero_add]
      field_simp
      ring
    simp only [hu]
    rw [e]
    positivity
  have hsum : ∑ i, c i * ‖u i‖ ^ 2 ≤ 1 := by
    have hA := sc_A_le N σ hw hf
    have e : ∑ i, c i * ‖u i‖ ^ 2 =
        ‖w‖ ^ 2 * ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc, hu, norm_div]
      ring
    rw [e]
    have hw2 : 0 < ‖w‖ ^ 2 := by
      have := norm_pos_iff.mpr hw0
      positivity
    calc _ ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hA hw2.le
      _ = 1 := mul_inv_cancel₀ hw2.ne'
  rw [hid, Complex.sub_re, Complex.one_re, Complex.re_sum]
  simp_rw [hre]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  by_cases hall : ∀ i, c i = 0
  · have : ∑ i, c i * ‖u i‖ ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    have : ∑ i, c i * (u i).im ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    linarith
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hcj : 0 < c j := lt_of_le_of_ne (hc0 j) (Ne.symm hj)
    have hpos : 0 < ∑ i, c i * (u i).im ^ 2 :=
      Finset.sum_pos' (fun i _ => mul_nonneg (hc0 i) (sq_nonneg _))
        ⟨j, Finset.mem_univ j, mul_pos hcj (pow_pos (huim j) 2)⟩
    linarith

/-! ## Existence -/

private lemma sc_exists (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, 0 < w.im ∧ fC N σ w = z := by
  set T : Set ℂ := {ζ | 0 < ζ.im ∧ ∃ w : ℂ, 0 < w.im ∧ fC N σ w = ζ} with hT
  have hpre : IsPreconnected upperHalf := (convex_halfSpace_im_gt 0).isPreconnected
  -- `T` is open: inverse function theorem at a preimage.
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    rintro ζ ⟨hζ, w, hw, rfl⟩
    have hstrict := sc_hasStrictDerivAt N σ hw
    have hne : fCDeriv N σ w ≠ 0 := by
      intro h0
      have := sc_re_pos N σ hw hζ.le
      rw [h0, mul_zero, Complex.zero_re] at this
      exact lt_irrefl _ this
    have h1 : fC N σ '' upperHalf ∈ 𝓝 (fC N σ w) := by
      rw [← hstrict.map_nhds_eq hne]
      exact image_mem_map (sc_isOpen_upperHalf.mem_nhds hw)
    have h2 : upperHalf ∈ 𝓝 (fC N σ w) := sc_isOpen_upperHalf.mem_nhds hζ
    filter_upwards [h1, h2] with ξ hξ1 hξ2
    obtain ⟨v, hv, rfl⟩ := hξ1
    exact ⟨hξ2, v, hv, rfl⟩
  -- `T` is nonempty: `f(i t)` with `t = (1 + N⁻¹ Σ σ_i²)⁻¹`.
  have hne : (upperHalf ∩ T).Nonempty := by
    set C : ℝ := ∑ i, σ i ^ 2 / N with hC
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => by positivity
    set t : ℝ := (1 + C)⁻¹ with ht
    have ht0 : 0 < t := by positivity
    set w : ℂ := (t : ℂ) * Complex.I with hw
    have hwim : w.im = t := by simp [hw]
    have hwn : ‖w‖ = t := by
      rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have hA : ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) ≤ C := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hB : 1 ≤ ‖1 + (σ i : ℂ) * w‖ := by
        have := Complex.re_le_norm (1 + (σ i : ℂ) * w)
        simpa [hw] using this
      rw [← div_div]
      exact div_le_self (by positivity) (one_le_pow₀ hB)
    have hpos : 0 < (fC N σ w).im := by
      rw [im_fC, hwim, hwn, ht, inv_pow, inv_inv]
      refine mul_pos (by positivity) ?_
      nlinarith
    exact ⟨fC N σ w, hpos, hpos, w, hwim ▸ ht0, rfl⟩
  -- `T` is relatively closed in `ℂ₊`: a priori bounds keep preimages in a compact subset.
  have hclosed : closure T ∩ upperHalf ⊆ T := by
    rintro z ⟨hzc, hz⟩
    change 0 < z.im at hz
    set S := ∑ i, σ i with hSdef
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hσ i
    have hzn : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
    set δ : ℝ := 1 / (2 * (1 + S) + 2 * ‖z‖) with hδ
    have hδpos : 0 < δ := by positivity
    set K : Set ℂ := {w | ‖w‖ ≤ 2 / z.im ∧ z.im / 2 * δ ^ 2 ≤ w.im} with hK
    have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im))
      ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 / z.im)).subset
        fun w hw => mem_closedBall_zero_iff.mpr hw.1)
    have hKpos : ∀ w ∈ K, 0 < w.im := fun w hw => lt_of_lt_of_le (by positivity) hw.2
    have hcont : ContinuousOn (fC N σ) K := continuousOn_of_forall_continuousAt fun w hw =>
      (sc_hasDerivAt N σ (hKpos w hw)).continuousAt
    have hKimg : IsClosed (fC N σ '' K) := (hKc.image_of_continuousOn hcont).isClosed
    have hsub : Metric.ball z (z.im / 2) ∩ T ⊆ fC N σ '' K := by
      rintro ζ ⟨hball, -, w, hw, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hball
      have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (sc_ne_zero hw)
      have him : z.im / 2 ≤ (fC N σ w).im := by
        have h := Complex.abs_im_le_norm (fC N σ w - z)
        rw [Complex.sub_im] at h
        have := (abs_le.mp h).1
        linarith
      have hnorm : ‖fC N σ w‖ ≤ 2 * ‖z‖ := by
        have h' : ‖fC N σ w‖ ≤ ‖z‖ + ‖fC N σ w - z‖ := by
          have := norm_add_le z (fC N σ w - z)
          rwa [add_sub_cancel] at this
        linarith [Complex.im_le_norm z]
      have hlow := sc_norm_lower N σ hσ hw
      have hδw : δ ≤ ‖w‖ := le_trans
        (one_div_le_one_div_of_le (by positivity) (by linarith)) hlow
      have hib := sc_im_bound N σ hw
      refine ⟨w, ⟨?_, ?_⟩, rfl⟩
      · have hup : (fC N σ w).im * ‖w‖ ≤ 1 := by
          by_contra hc
          push Not at hc
          have := mul_lt_mul_of_pos_right hc hw0
          nlinarith [Complex.im_le_norm w]
        rw [le_div_iff₀ hz]
        nlinarith [mul_le_mul_of_nonneg_right him hw0.le]
      · calc z.im / 2 * δ ^ 2 ≤ (fC N σ w).im * ‖w‖ ^ 2 :=
              mul_le_mul him (pow_le_pow_left₀ hδpos.le hδw 2) (by positivity) (by linarith)
          _ ≤ w.im := hib
    have hzK : z ∈ fC N σ '' K := by
      have h1 : z ∈ closure (Metric.ball z (z.im / 2) ∩ T) :=
        Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self (by positivity), hzc⟩
      exact closure_minimal hsub hKimg h1
    obtain ⟨w, hwK, hwz⟩ := hzK
    exact ⟨hz, w, hKpos w hwK, hwz⟩
  exact (hpre.subset_of_closure_inter_subset hopen hne hclosed (show z ∈ upperHalf from hz)).2

/-! ## The bound `|f(w)| ≤ (1 + √R) / |w|` -/

private lemma sc_norm_fC_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {w : ℂ}
    (hw : 0 < w.im) (hf : 0 ≤ (fC N σ w).im) :
    ‖fC N σ w‖ ≤ (1 + √(massRatio N σ)) / ‖w‖ := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (sc_ne_zero hw)
  set r : Fin M → ℝ := fun i => σ i / (N * ‖1 + (σ i : ℂ) * w‖) with hr
  set p : Fin M → ℝ := fun i => (if 0 < σ i then (1 : ℝ) else 0) / N with hp
  set g : Fin M → ℝ := fun i => σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2) with hg
  have h1 : ‖fC N σ w‖ ≤ ‖w‖⁻¹ + ∑ i, r i := by
    unfold fC
    refine (norm_add_le _ _).trans (add_le_add (by rw [norm_neg, norm_inv])
      ((norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))))
    simp [hr, abs_of_nonneg (hσ i)]
  have hpsum : ∑ i, p i = massRatio N σ := by
    simp only [hp, ← Finset.sum_div, Finset.sum_boole]
    rfl
  have hCS : (∑ i, r i) ^ 2 ≤ (∑ i, p i) * ∑ i, g i := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => ?_)
      (fun i _ => by positivity) (fun i _ => ?_)
    · simp only [hp]
      split_ifs <;> positivity
    · rcases (hσ i).eq_or_lt with h0 | hpos
      · simp [hr, hp, hg, ← h0]
      · simp only [hr, hp, hg, hpos, ite_true]
        exact le_of_eq (by ring)
  have hA := sc_A_le N σ hw hf
  have hR : 0 ≤ massRatio N σ := by
    unfold massRatio
    positivity
  have h2 : ∑ i, r i ≤ √(massRatio N σ) / ‖w‖ := by
    have hsq : (∑ i, r i) ^ 2 ≤ massRatio N σ * (‖w‖ ^ 2)⁻¹ := by
      rw [← hpsum]
      exact hCS.trans (mul_le_mul_of_nonneg_left hA (hpsum ▸ hR))
    have := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
    rwa [Real.sqrt_mul hR, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg w), ← div_eq_mul_inv]
      at this
  rw [add_div, one_div]
  linarith

/-! ## Existence and uniqueness of `m` (Lemma 2.2, Definition 2.3, (def_m)) -/

theorem mFun_spec (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    0 < (mFun N σ z).im ∧ fC N σ (mFun N σ z) = z := by
  have h : ∃ w : ℂ, 0 < w.im ∧ fC N σ w = z := sc_exists N σ hσ hz
  rw [mFun, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem mFun_eq_of_fC_eq (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (h : fC N σ w = z) : mFun N σ z = w := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  exact sc_unique N σ hm hw (by rw [hfm]; exact hz) (hfm.trans h.symm)

/-- The global bound `|m(z)| ≤ (1 + √R) / |z|` on `ℂ₊`. -/
theorem norm_mFun_le (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    ‖mFun N σ z‖ ≤ (1 + √(massRatio N σ)) / ‖z‖ := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  have hb := sc_norm_fC_le N σ hσ hm (by rw [hfm]; exact hz.le)
  rw [hfm] at hb
  have hm0 : 0 < ‖mFun N σ z‖ := norm_pos_iff.mpr (sc_ne_zero hm)
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
  rw [le_div_iff₀ hm0] at hb
  rw [le_div_iff₀ hzn, mul_comm]
  exact hb

/-- `f'(w) ≠ 0` for `w ∈ ℂ₊` with `Im f(w) ≥ 0`. -/
theorem fCDeriv_ne_zero (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {w : ℂ} (hw : 0 < w.im)
    (hf : 0 ≤ (fC N σ w).im) : fCDeriv N σ w ≠ 0 := by
  intro h0
  have := sc_re_pos N σ hw hf
  rw [h0, mul_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem hasDerivAt_mFun (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mFun N σ) (fCDeriv N σ (mFun N σ z))⁻¹ z := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  have hstrict := sc_hasStrictDerivAt N σ hm
  have hne : fCDeriv N σ (mFun N σ z) ≠ 0 := fCDeriv_ne_zero N σ hσ hm (by rw [hfm]; exact hz.le)
  have hev : ∀ᶠ x in 𝓝 (mFun N σ z), mFun N σ (fC N σ x) = x := by
    have h1 : upperHalf ∈ 𝓝 (mFun N σ z) := sc_isOpen_upperHalf.mem_nhds hm
    have h2 : fC N σ ⁻¹' upperHalf ∈ 𝓝 (mFun N σ z) :=
      hstrict.hasDerivAt.continuousAt.preimage_mem_nhds
        (sc_isOpen_upperHalf.mem_nhds (show 0 < (fC N σ (mFun N σ z)).im by rw [hfm]; exact hz))
    filter_upwards [h1, h2] with x hx1 hx2
    exact mFun_eq_of_fC_eq N σ hσ hx2 hx1 rfl
  have h := (hstrict.to_local_left_inverse hne hev).hasDerivAt
  rwa [hfm] at h

theorem analyticOnNhd_mFun (N : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    AnalyticOnNhd ℂ (mFun N σ) upperHalf :=
  DifferentiableOn.analyticOnNhd (fun _ hz =>
    (hasDerivAt_mFun N σ hσ hz).differentiableAt.differentiableWithinAt) sc_isOpen_upperHalf

/-! ## Concrete instance (Marchenko–Pastur: `M = 1`, `N = 2`, `σ = 1`, `z = i`) -/

example : 0 < (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I).im ∧
    fC 2 (fun _ : Fin 1 => (1 : ℝ)) (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I) = Complex.I :=
  mFun_spec 2 _ (fun _ => by norm_num) (by simp)

example : ‖mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I‖ ≤
    (1 + √(massRatio 2 (fun _ : Fin 1 => (1 : ℝ)))) / ‖Complex.I‖ :=
  norm_mFun_le 2 _ (fun _ => by norm_num) (by simp)

example : fCDeriv 2 (fun _ : Fin 1 => (1 : ℝ)) (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I) ≠ 0 :=
  fCDeriv_ne_zero 2 _ (fun _ => by norm_num)
    (mFun_spec 2 _ (fun _ => by norm_num) (by simp)).1
    (by rw [(mFun_spec 2 _ (fun _ => by norm_num) (by simp)).2]; simp)

example : HasDerivAt (mFun 2 (fun _ : Fin 1 => (1 : ℝ)))
    (fCDeriv 2 (fun _ : Fin 1 => (1 : ℝ)) (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I))⁻¹
      Complex.I :=
  hasDerivAt_mFun 2 _ (fun _ => by norm_num) (by simp)

example : AnalyticOnNhd ℂ (mFun 2 (fun _ : Fin 1 => (1 : ℝ))) upperHalf :=
  analyticOnNhd_mFun 2 _ (fun _ => by norm_num)

end Anisotropic
