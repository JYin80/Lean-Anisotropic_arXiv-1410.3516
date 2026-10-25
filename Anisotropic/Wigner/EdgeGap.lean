import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The critical point `x₊` stays away from the spectrum of `A` -/

/-- `|b − (x + iy)|² = (b − x)² + y²`. -/
private lemma edgeGap_normSq (b x y : ℝ) :
    Complex.normSq ((b : ℂ) - ⟨x, y⟩) = (b - x) ^ 2 + y ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  ring

/-- `Im m_A(w) = Im w · N⁻¹ ∑ᵢ |aᵢ − w|⁻²`. -/
private lemma edgeGap_im_stieltjesA {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    (stieltjesA a w).im = w.im * ((N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹) := by
  unfold stieltjesA
  rw [show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
    Complex.im_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-- `‖m_A(w)‖ ≤ (N⁻¹ ∑ᵢ |aᵢ − w|⁻² + 1)/2` for `N ≥ 1`. -/
private lemma edgeGap_norm_stieltjesA_le {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) (w : ℂ) :
    ‖stieltjesA a w‖ ≤ ((N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ + 1) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ‖stieltjesA a w‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖ := by
    unfold stieltjesA
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have hle : ∑ i, ‖((a i : ℂ) - w)⁻¹‖ ≤
      ∑ i, ((Complex.normSq ((a i : ℂ) - w))⁻¹ + 1) / 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Complex.sq_norm, ← inv_pow, ← norm_inv]
    nlinarith [sq_nonneg (‖((a i : ℂ) - w)⁻¹‖ - 1)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hle
  calc ‖stieltjesA a w‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖ := h1
    _ ≤ (N : ℝ)⁻¹ * ((∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ + N) / 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp

/-- Right edge, pointwise: if `τ ≤ 1/2`, `N^{−1+τ} ≤ τ³/64`, `|aᵢ| ≤ τ⁻¹ − 2` and the standing
bound holds on `𝐃^W(τ, N)`, then every `x > maxᵢ aᵢ` with `S(x) ≤ 1` satisfies
`x ≥ maxᵢ aᵢ + τ/4`. Otherwise `w = maxᵢ aᵢ + τ/2 + iτ/4` has `S(w) ≤ 1 − τ²/16`, so
`z = w − m_A(w)` lies in `𝐃^W(τ, N)` with `z + m^W(z) = w`, and `|maxᵢ aᵢ − w| < τ` contradicts the
standing bound at `z` (§12.4). -/
private lemma edgeGap_right {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    (hNτ : (N : ℝ) ^ (-1 + τ) ≤ τ ^ 3 / 64) {a : Fin N → ℝ} (ha : ∀ i, |a i| ≤ τ⁻¹ - 2)
    (hS : StandingBoundW τ a (domW τ N)) {x : ℝ} (hx1 : (⨆ i, a i) < x) (hsx : sW a x ≤ 1) :
    (⨆ i, a i) + τ / 4 ≤ x := by
  by_contra hx2
  push Not at hx2
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  have hα1 := abs_le.1 (ha i₀)
  rw [hi₀] at hα1
  have hτinv : 2 ≤ τ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτ]; linarith
  set w : ℂ := ⟨α + τ / 2, τ / 4⟩ with hw
  set S := (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ with hSdef
  -- each term of `S(w)` is at most `(1 − τ²/16) (x − aᵢ)⁻²`
  have hterm : ∀ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ ≤ (1 - τ ^ 2 / 16) * ((a i - x) ^ 2)⁻¹ := by
    intro i
    rw [hw, edgeGap_normSq]
    have hd0 : 0 < x - a i := by linarith [hle i]
    have hd1 : (x - a i) * τ < 2 := by
      have := abs_le.1 (ha i)
      have h3 : x - a i < 2 * τ⁻¹ := by linarith
      calc (x - a i) * τ < 2 * τ⁻¹ * τ := mul_lt_mul_of_pos_right h3 hτ
        _ = 2 := by field_simp
    set d := x - a i with hd
    have hD : d * (1 + τ ^ 2 / 8) ≤ α + τ / 2 - a i := by nlinarith
    have hD2 : d ^ 2 ≤ (1 - τ ^ 2 / 16) * ((a i - (α + τ / 2)) ^ 2 + (τ / 4) ^ 2) := by
      have h4 : (d * (1 + τ ^ 2 / 8)) ^ 2 ≤ (α + τ / 2 - a i) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hD 2
      have h5 : d ^ 2 ≤ (1 - τ ^ 2 / 16) * (d * (1 + τ ^ 2 / 8)) ^ 2 := by
        have ht : τ ^ 2 ≤ 1 / 4 := by nlinarith
        have : 1 ≤ (1 - τ ^ 2 / 16) * (1 + τ ^ 2 / 8) ^ 2 := by
          have e : (1 - τ ^ 2 / 16) * (1 + τ ^ 2 / 8) ^ 2 - 1 =
              τ ^ 2 / 8 * (3 / 2 - (τ ^ 2 / 8) ^ 2 / 2) := by ring
          have h7 : 0 ≤ τ ^ 2 / 8 * (3 / 2 - (τ ^ 2 / 8) ^ 2 / 2) := by
            apply mul_nonneg (by positivity)
            nlinarith [sq_nonneg τ]
          linarith
        nlinarith [sq_nonneg d]
      have h6 : 0 ≤ 1 - τ ^ 2 / 16 := by nlinarith
      nlinarith [sq_nonneg (τ / 4), mul_nonneg h6 (sq_nonneg (τ / 4))]
    have hpos : 0 < (a i - (α + τ / 2)) ^ 2 + (τ / 4) ^ 2 := by positivity
    have hd2 : (a i - x) ^ 2 = d ^ 2 := by rw [hd]; ring
    rw [hd2, ← div_eq_mul_inv]
    rw [inv_eq_one_div, div_le_div_iff₀ hpos (by positivity)]
    linarith
  have hSle : S ≤ 1 - τ ^ 2 / 16 := by
    have hsum : ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ ≤
        (1 - τ ^ 2 / 16) * ∑ i, ((a i - x) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hterm i
    have h1 : S ≤ (1 - τ ^ 2 / 16) * sW a x := by
      rw [hSdef, sW]
      calc (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹
          ≤ (N : ℝ)⁻¹ * ((1 - τ ^ 2 / 16) * ∑ i, ((a i - x) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    have h6 : 0 ≤ 1 - τ ^ 2 / 16 := by nlinarith
    nlinarith
  have hSpos : 0 < S := by
    rw [hSdef]
    refine mul_pos (inv_pos.2 hNpos) (Finset.sum_pos (fun i _ => inv_pos.2 ?_) ⟨i₀, by simp⟩)
    rw [hw, edgeGap_normSq]; positivity
  have hS1 : S < 1 := by have := pow_pos hτ 2; linarith
  set m := stieltjesA a w with hm
  set z := w - m with hz
  have hmim : m.im = τ / 4 * S := by rw [hm, edgeGap_im_stieltjesA]
  have hzim : z.im = τ / 4 * (1 - S) := by
    rw [hz, Complex.sub_im, hmim]; simp only [hw]; ring
  have hmn : ‖m‖ ≤ 1 := by
    have h := edgeGap_norm_stieltjesA_le hN a w
    rw [← hSdef, ← hm] at h
    linarith
  have hmre : |m.re| ≤ 1 := (Complex.abs_re_le_norm m).trans hmn
  have hzre : z.re = α + τ / 2 - m.re := by rw [hz, Complex.sub_re]
  have hzpos : 0 < z.im := by rw [hzim]; exact mul_pos (by positivity) (by linarith)
  have hzD : z ∈ domW τ N := by
    refine ⟨hzpos, ?_, ?_, ?_⟩
    · rw [hzre, abs_le]
      have := abs_le.1 hmre
      constructor <;> linarith
    · rw [hzim]
      have : τ ^ 3 / 64 ≤ τ / 4 * (1 - S) := by
        have : τ ^ 2 / 16 ≤ 1 - S := by linarith
        calc τ ^ 3 / 64 = τ / 4 * (τ ^ 2 / 16) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    · rw [hzim]
      have : τ / 4 * (1 - S) ≤ τ / 4 := by nlinarith
      linarith
  have hzm : z + m = w := by rw [hz]; ring
  have hmW : mW a z = m :=
    mW_eq_of_spec hN a hzpos (by rw [hmim]; positivity) (by rw [hzm])
  have hb := hS z hzD i₀
  rw [hmW, show -m + (a i₀ : ℂ) - z = (a i₀ : ℂ) - (z + m) by ring, hzm] at hb
  have hsq : ‖(a i₀ : ℂ) - w‖ ^ 2 = (τ / 2) ^ 2 + (τ / 4) ^ 2 := by
    rw [Complex.sq_norm, hw, edgeGap_normSq, hi₀]; ring
  have : τ ^ 2 ≤ ‖(a i₀ : ℂ) - w‖ ^ 2 := pow_le_pow_left₀ hτ.le hb 2
  nlinarith

/-- `S(maxᵢ aᵢ + 1) ≤ 1`, so the set defining `x₊` is nonempty. -/
private lemma edgeGap_sW_le_one {N : ℕ} (a : Fin N → ℝ) : sW a ((⨆ i, a i) + 1) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp [sW]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
  unfold sW
  have h : ∀ i, ((a i - ((⨆ i, a i) + 1)) ^ 2)⁻¹ ≤ 1 := by
    intro i
    have := le_ciSup (Set.finite_range a).bddAbove i
    apply inv_le_one_of_one_le₀
    nlinarith
  calc (N : ℝ)⁻¹ * ∑ i, ((a i - ((⨆ i, a i) + 1)) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)
    _ = 1 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]; field_simp

/-- Right edge: `maxᵢ aᵢ + τ/4 ≤ x₊` under the hypotheses of the pointwise form. -/
private lemma edgeGap_right_le {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    (hNτ : (N : ℝ) ^ (-1 + τ) ≤ τ ^ 3 / 64) {a : Fin N → ℝ} (ha : ∀ i, |a i| ≤ τ⁻¹ - 2)
    (hS : StandingBoundW τ a (domW τ N)) : (⨆ i, a i) + τ / 4 ≤ xpW a := by
  unfold xpW
  apply le_csInf
  · exact ⟨(⨆ i, a i) + 1, by linarith, edgeGap_sW_le_one a⟩
  · rintro x ⟨hx1, hx2⟩
    exact edgeGap_right hN hτ hτ2 hNτ ha hS hx1 hx2

/-- `range(−a) = −range(a)`. -/
private lemma edgeGap_range_neg {N : ℕ} (a : Fin N → ℝ) : Set.range (-a) = -Set.range a := by
  ext x
  simp only [Set.mem_range, Set.mem_neg, Pi.neg_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by linarith⟩

/-- `maxᵢ (−aᵢ) = −minᵢ aᵢ`. -/
private lemma edgeGap_iSup_neg {N : ℕ} (a : Fin N → ℝ) : (⨆ i, (-a) i) = -⨅ i, a i := by
  change sSup (Set.range (-a)) = -sInf (Set.range a)
  rw [edgeGap_range_neg, Real.sSup_neg]

/-- `S_{−a}(x) = S_a(−x)`. -/
private lemma edgeGap_sW_neg {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : sW (-a) x = sW a (-x) := by
  unfold sW
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Pi.neg_apply]
  ring

/-- Reflection of the critical points: `x₊(−a) = −x₋(a)`. -/
private lemma edgeGap_xpW_neg {N : ℕ} (a : Fin N → ℝ) : xpW (-a) = -xmW a := by
  unfold xpW xmW
  have : {x : ℝ | (⨆ i, (-a) i) < x ∧ sW (-a) x ≤ 1} =
      -{y : ℝ | y < (⨅ i, a i) ∧ sW a y ≤ 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_neg, edgeGap_iSup_neg, edgeGap_sW_neg]
    rw [neg_lt]
  rw [this, Real.sInf_neg]

/-- The standing bound on `𝐃^W(τ, N)` is invariant under `a ↦ −a` (through `z ↦ −z̄`). -/
private lemma edgeGap_standing_neg {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} {a : Fin N → ℝ}
    (hS : StandingBoundW τ a (domW τ N)) : StandingBoundW τ (-a) (domW τ N) := by
  intro z hz i
  have hz'D : -(starRingEnd ℂ) z ∈ domW τ N := by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im, neg_neg,
        abs_neg] <;> assumption
  have hm := mW_neg hN a hz'D.1
  simp only [map_neg, Complex.conj_conj, neg_neg] at hm
  rw [hm]
  have hb := hS _ hz'D i
  have e : -(-(starRingEnd ℂ) (mW a (-(starRingEnd ℂ) z))) + (((-a) i : ℝ) : ℂ) - z =
      -(starRingEnd ℂ) (-(mW a (-(starRingEnd ℂ) z)) + (a i : ℂ) - -(starRingEnd ℂ) z) := by
    simp only [map_neg, map_sub, map_add, Complex.conj_conj, Complex.conj_ofReal, Pi.neg_apply,
      Complex.ofReal_neg]
    ring
  rw [e, norm_neg, Complex.norm_conj]
  exact hb

/-- Under `|aᵢ| ≤ τ⁻¹ − 2` and the standing bound on `𝐃^W(τ, N)`, the critical points `x±` of `g`
lie at distance at least `τ/4` from the spectrum of `A` (§12.4). -/
theorem xpW_sub_ge {τ : ℝ} (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ, (∀ i, |a i| ≤ τ⁻¹ - 2) →
      StandingBoundW τ a (domW τ N) →
      (⨆ i, a i) + τ / 4 ≤ xpW a ∧ xmW a ≤ (⨅ i, a i) - τ / 4 := by
  by_cases hτ2 : τ ≤ 1 / 2
  · have hlt : 0 < 1 - τ := by linarith
    have ht := (tendsto_rpow_neg_atTop hlt).comp tendsto_natCast_atTop_atTop
    have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < τ ^ 3 / 64 by positivity))
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
    refine ⟨max N₁ 1, fun N hN a ha hS => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNτ : (N : ℝ) ^ (-1 + τ) ≤ τ ^ 3 / 64 := by
      have := hN₁ N (le_of_max_le_left hN)
      simp only [Function.comp] at this
      rw [show -1 + τ = -(1 - τ) by ring]
      exact this.le
    refine ⟨edgeGap_right_le hN1 hτ hτ2 hNτ ha hS, ?_⟩
    have ha' : ∀ i, |(-a) i| ≤ τ⁻¹ - 2 := fun i => by simpa using ha i
    have h := edgeGap_right_le hN1 hτ hτ2 hNτ ha' (edgeGap_standing_neg hN1 hS)
    rw [edgeGap_iSup_neg, edgeGap_xpW_neg] at h
    linarith
  · refine ⟨1, fun N hN a ha _ => ?_⟩
    have h1 := ha ⟨0, hN⟩
    have h2 : τ⁻¹ < 2 := by
      rw [inv_lt_comm₀ hτ (by norm_num)]
      linarith
    exact absurd (abs_nonneg (a ⟨0, hN⟩)) (by linarith)

end Anisotropic
