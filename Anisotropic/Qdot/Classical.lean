import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.SelfConsistent
import Anisotropic.Density.Stability.Bulk
import Anisotropic.Density.Stability.EdgeStab
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.Density.Varrho
import Anisotropic.Framework.Domination
import Anisotropic.Qdot.Defs
import Anisotropic.Rigidity.Defs
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Rigidity.Segment

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The classical quantities at `N − 1` against those at `N` -/

/-! ## The assumptions at `N − 1` -/

private lemma qc_cast_pred (hN : 2 ≤ N) : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega)]; simp

/-- (phi_bounded), (bound_Sigma), (Sigma_gap) at `N − 1` with `τ/2`, from those at `N` with `τ`. -/
private lemma qc_da_pred {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hN : 2 ≤ N) :
    DensityAssumptions (τ / 2) (N - 1) σ := by
  have hτ := h.pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := qc_cast_pred hN
  have hφl := h.phi_lower
  have hφu := h.phi_upper
  unfold phiRatio at hφl hφu
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  refine ⟨by positivity, h.nonneg, ?_, ?_, ?_, ?_⟩
  · unfold phiRatio
    rw [hc, le_div_iff₀ hN1]
    rw [le_div_iff₀ (by linarith)] at hφl
    nlinarith
  · unfold phiRatio
    rw [hc, div_le_iff₀ hN1]
    rw [div_le_iff₀ (by linarith)] at hφu
    have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
    rw [this]
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    nlinarith
  · intro i
    have := h.bound_Sigma i
    have : τ⁻¹ ≤ (τ / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    linarith
  · have := (h.mono (show 0 < τ / 2 by positivity) (by linarith)).Sigma_gap
    linarith

private lemma qc_posVals_nonempty {τ : ℝ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    (posVals σ).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ i, σ i = 0 := by
    intro i
    rcases (h.nonneg i).eq_or_lt with h0 | hpos
    · exact h0.symm
    · have : σ i ∈ posVals σ :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hpos⟩
      rw [hne] at this
      exact absurd this (Finset.notMem_empty _)
  have hτ := h.pos
  have hM : 0 < M := by
    by_contra h0
    have hM0 : M = 0 := by omega
    have := h.phi_lower
    unfold phiRatio at this
    rw [hM0] at this
    simp at this
    linarith
  have hgap := h.Sigma_gap
  have hfull : empMeasure σ (Set.Icc 0 τ) = 1 := by
    simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurableSet_Icc, smul_eq_mul]
    have : ∀ i, (Set.Icc 0 τ).indicator (1 : ℝ → ℝ≥0∞) (σ i) = 1 := by
      intro i
      rw [hall i]
      simp [Set.indicator, hτ.le]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hM.ne') (ENNReal.natCast_ne_top _)
  rw [hfull, ENNReal.toReal_one] at hgap
  linarith

/-! ## A Lipschitz bound for `m` on `ℂ₊` -/

/-- `f(w) − f(w') = (w − w') B` with `B = (w w')⁻¹ − N⁻¹ Σ_i σ_i² / ((1 + σ_i w)(1 + σ_i w'))`. -/
private lemma qc_fC_sub (K : ℕ) (σ : Fin M → ℝ) {w w' : ℂ} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (h1 : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (h1' : ∀ i, 1 + (σ i : ℂ) * w' ≠ 0) :
    fC K σ w - fC K σ w' = (w - w') * ((w * w')⁻¹ -
      ∑ i, (σ i : ℂ) ^ 2 / (K * ((1 + σ i * w) * (1 + σ i * w')))) := by
  unfold fC
  rw [mul_sub, Finset.mul_sum]
  have hsum : ∑ i, (σ i : ℂ) / (K * (1 + σ i * w)) - ∑ i, (σ i : ℂ) / (K * (1 + σ i * w')) =
      -∑ i, (w - w') * ((σ i : ℂ) ^ 2 / (K * ((1 + σ i * w) * (1 + σ i * w')))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    have a := h1 i
    have b := h1' i
    field_simp
    ring
  have e1 : -w⁻¹ - -w'⁻¹ = (w - w') * (w * w')⁻¹ := by
    field_simp
    ring
  linear_combination e1 + hsum

private lemma qc_one_add_ne {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {w : ℂ} (hw : 0 < w.im)
    (i : Fin M) :
    1 + (σ i : ℂ) * w ≠ 0 := by
  intro h
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0] at h; simp at h
  · have := congrArg Complex.im h
    simp at this
    rcases this with h' | h'
    · linarith
    · linarith

private lemma qc_ne_zero_of_im {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := by
  rintro rfl; simp at hw

/-- `|m(z) − m(z')|² Im z Im z' ≤ |z − z'|² Im m(z) Im m(z')` on `ℂ₊`. -/
private lemma qc_m_lip (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {z z' : ℂ} (hz : 0 < z.im)
    (hz' : 0 < z'.im) :
    ‖mFun K σ z - mFun K σ z'‖ ^ 2 * (z.im * z'.im) ≤
      ‖z - z'‖ ^ 2 * ((mFun K σ z).im * (mFun K σ z').im) := by
  obtain ⟨hm, hfm⟩ := mFun_spec K σ hσ hz
  obtain ⟨hm', hfm'⟩ := mFun_spec K σ hσ hz'
  set m := mFun K σ z with hmdef
  set m' := mFun K σ z' with hm'def
  have hm0 := qc_ne_zero_of_im hm
  have hm0' := qc_ne_zero_of_im hm'
  have h1 := qc_one_add_ne hσ hm
  have h1' := qc_one_add_ne hσ hm'
  have hid := qc_fC_sub K σ hm0 hm0' h1 h1'
  rw [hfm, hfm'] at hid
  set B := (m * m')⁻¹ - ∑ i, (σ i : ℂ) ^ 2 / (K * ((1 + σ i * m) * (1 + σ i * m')))
  -- the quantities
  set a := (‖m‖ ^ 2)⁻¹ with ha
  set b := (‖m'‖ ^ 2)⁻¹ with hb
  set A := ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * m‖ ^ 2) with hA
  set A' := ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * m'‖ ^ 2) with hA'
  have him := im_fC K σ m
  have him' := im_fC K σ m'
  rw [hfm] at him
  rw [hfm'] at him'
  have hnm : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hnm' : 0 < ‖m'‖ := norm_pos_iff.mpr hm0'
  set u := z.im / m.im with hu
  set v := z'.im / m'.im with hv
  have hu0 : 0 < u := div_pos hz hm
  have hv0 : 0 < v := div_pos hz' hm'
  have him2 : z.im = m.im * (a - A) := him
  have him2' : z'.im = m'.im * (b - A') := him'
  have hAu : a - A = u := by rw [hu, him2, mul_div_cancel_left₀ _ hm.ne']
  have hAv : b - A' = v := by rw [hv, him2', mul_div_cancel_left₀ _ hm'.ne']
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hA0' : 0 ≤ A' := Finset.sum_nonneg fun i _ => by positivity
  -- `S ≤ √(A A')`
  set S := ∑ i, σ i ^ 2 / (K * (‖1 + (σ i : ℂ) * m‖ * ‖1 + (σ i : ℂ) * m'‖)) with hS
  set p := (‖m‖ * ‖m'‖)⁻¹ with hp
  have hp2 : p ^ 2 = a * b := by rw [hp, ha, hb]; field_simp
  have hp0 : 0 < p := by positivity
  have hBS : p - S ≤ ‖B‖ := by
    have e1 : ‖(m * m')⁻¹‖ = p := by rw [norm_inv, norm_mul]
    have e2 : ‖∑ i, (σ i : ℂ) ^ 2 / (K * ((1 + σ i * m) * (1 + σ i * m')))‖ ≤ S := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    have := norm_sub_norm_le ((m * m')⁻¹)
      (∑ i, (σ i : ℂ) ^ 2 / (K * ((1 + σ i * m) * (1 + σ i * m'))))
    rw [e1] at this
    linarith
  rcases Nat.eq_zero_or_pos K with hK | hK
  · -- `K = 0`: then `A = A' = S = 0`
    subst hK
    have hA00 : A = 0 := by simp [hA]
    have hA00' : A' = 0 := by simp [hA']
    have hS0 : S = 0 := by simp [hS]
    rw [hS0, sub_zero] at hBS
    have hz2 : ‖z - z'‖ = ‖m - m'‖ * ‖B‖ := by rw [hid, norm_mul]
    have hpB : p ^ 2 ≤ ‖B‖ ^ 2 := pow_le_pow_left₀ hp0.le hBS 2
    have hab : a * b = u * v := by rw [← hAu, ← hAv, hA00, hA00']; ring
    rw [hz2, mul_pow]
    have hq : z.im * z'.im = u * v * (m.im * m'.im) := by
      rw [hu, hv]; field_simp
    rw [hq]
    have hmm : 0 < m.im * m'.im := mul_pos hm hm'
    have key : u * v ≤ ‖B‖ ^ 2 := by rw [← hab, ← hp2]; exact hpB
    have e1 : ‖m - m'‖ ^ 2 * (u * v * (m.im * m'.im)) =
        (‖m - m'‖ ^ 2 * (m.im * m'.im)) * (u * v) := by ring
    have e2 : ‖m - m'‖ ^ 2 * ‖B‖ ^ 2 * (m.im * m'.im) =
        (‖m - m'‖ ^ 2 * (m.im * m'.im)) * ‖B‖ ^ 2 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hCS : S ^ 2 ≤ A * A' := by
    have e : S = (K : ℝ)⁻¹ * ∑ i, (σ i / ‖1 + (σ i : ℂ) * m‖) * (σ i / ‖1 + (σ i : ℂ) * m'‖) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have eA : A = (K : ℝ)⁻¹ * ∑ i, (σ i / ‖1 + (σ i : ℂ) * m‖) ^ 2 := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have eA' : A' = (K : ℝ)⁻¹ * ∑ i, (σ i / ‖1 + (σ i : ℂ) * m'‖) ^ 2 := by
      rw [hA', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [e, eA, eA', mul_pow]
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => σ i / ‖1 + (σ i : ℂ) * m‖)
      (fun i => σ i / ‖1 + (σ i : ℂ) * m'‖)
    have hk : 0 ≤ (K : ℝ)⁻¹ ^ 2 := by positivity
    calc (K : ℝ)⁻¹ ^ 2 * (∑ i, σ i / ‖1 + (σ i : ℂ) * m‖ * (σ i / ‖1 + (σ i : ℂ) * m'‖)) ^ 2
        ≤ (K : ℝ)⁻¹ ^ 2 * ((∑ i, (σ i / ‖1 + (σ i : ℂ) * m‖) ^ 2) *
            ∑ i, (σ i / ‖1 + (σ i : ℂ) * m'‖) ^ 2) := mul_le_mul_of_nonneg_left this hk
      _ = _ := by ring
  set Q := Real.sqrt (A * A') with hQ
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hQ2 : Q ^ 2 = A * A' := Real.sq_sqrt (mul_nonneg hA0 hA0')
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hSQ : S ≤ Q := by
    rw [hQ]; exact Real.le_sqrt_of_sq_le hCS
  -- `(p − Q)² ≥ u v`
  have haA : A ≤ a := by linarith
  have hbA : A' ≤ b := by linarith
  have hQp : Q ≤ p := by
    have : Q ^ 2 ≤ p ^ 2 := by
      rw [hQ2, hp2]
      exact mul_le_mul haA hbA hA0' (by linarith)
    exact (pow_le_pow_iff_left₀ hQ0 hp0.le (by norm_num)).mp this
  have hkey : 2 * (p * Q) ≤ 2 * (a * b) - a * v - b * u := by
    have h0 : 0 ≤ 2 * (a * b) - a * v - b * u := by nlinarith
    have hsq : (2 * (p * Q)) ^ 2 ≤ (2 * (a * b) - a * v - b * u) ^ 2 := by
      have e : (2 * (p * Q)) ^ 2 = 4 * (a * (b - v)) * (b * (a - u)) := by
        rw [mul_pow, mul_pow, hp2, hQ2, ← hAu, ← hAv]; ring
      rw [e]
      have e2 : 2 * (a * b) - a * v - b * u = a * (b - v) + b * (a - u) := by ring
      rw [e2]
      nlinarith [sq_nonneg (a * (b - v) - b * (a - u))]
    exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).mp hsq
  have hpq : u * v ≤ (p - Q) ^ 2 := by
    have e : (p - Q) ^ 2 = a * b + A * A' - 2 * (p * Q) := by rw [sub_sq, hp2, hQ2]; ring
    have hA1 : A = a - u := by linarith
    have hA2 : A' = b - v := by linarith
    rw [e, hA1, hA2]
    have e3 : a * b + (a - u) * (b - v) - 2 * (p * Q) =
        (2 * (a * b) - a * v - b * u - 2 * (p * Q)) + u * v := by ring
    rw [e3]
    linarith
  have hBpq : (p - Q) ^ 2 ≤ ‖B‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hz2 : ‖z - z'‖ = ‖m - m'‖ * ‖B‖ := by rw [hid, norm_mul]
  rw [hz2, mul_pow]
  have hq : z.im * z'.im = u * v * (m.im * m'.im) := by
    rw [hu, hv]; field_simp
  rw [hq]
  have hmm : 0 < m.im * m'.im := mul_pos hm hm'
  have key : u * v ≤ ‖B‖ ^ 2 := hpq.trans hBpq
  have e1 : ‖m - m'‖ ^ 2 * (u * v * (m.im * m'.im)) =
      (‖m - m'‖ ^ 2 * (m.im * m'.im)) * (u * v) := by ring
  have e2 : ‖m - m'‖ ^ 2 * ‖B‖ ^ 2 * (m.im * m'.im) =
      (‖m - m'‖ ^ 2 * (m.im * m'.im)) * ‖B‖ ^ 2 := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-! ## `m_{N−1}` against `m_N` on `ℂ₊` -/

/-- `|m_{N−1}(z) − m_N(z)| ≤ C/(Nη)` for `τ ≤ |z| ≤ τ⁻¹` (no regularity). -/
theorem mFun_pred_sub (τ : ℝ) (hτ : 0 < τ) :
    ∃ C₀ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ z : ℂ, 0 < z.im → τ ≤ ‖z‖ → ‖z‖ ≤ τ⁻¹ →
        ‖mFun (N - 1) σ z - mFun N σ z‖ ≤ C₀ / (N * z.im) := by
  set C := genPropConst (τ / 2) with hCdef
  have hC : 0 < C := by rw [hCdef, genPropConst]; positivity
  set D := τ⁻¹ + C with hDdef
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hD : 0 < D := by positivity
  refine ⟨2 * C * D, ⌈2 * D / τ + D * τ⌉₊ + 2, ?_⟩
  intro N hN M σ h z hz hz1 hz2
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNc : 2 * D / τ + D * τ ≤ N := by
    have := Nat.le_ceil (2 * D / τ + D * τ)
    have h' : ((⌈2 * D / τ + D * τ⌉₊ + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h'
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hσ := h.nonneg
  have h2 := h.mono (show 0 < τ / 2 by positivity) (by linarith)
  have h1 := qc_da_pred h hN2
  have hτ2 : τ / 2 ≤ τ := by linarith
  have hτi2 : τ⁻¹ ≤ (τ / 2)⁻¹ := inv_anti₀ (by positivity) hτ2
  -- `w = m_{N−1}(z)` and the subordinate point `z'`
  obtain ⟨hw1, -, -⟩ := gen_prop_m h1 hz (hτ2.trans hz1) (hz2.trans hτi2)
  set w := mFun (N - 1) σ z with hwdef
  obtain ⟨hwim, -⟩ := mFun_spec (N - 1) σ hσ hz
  have hw0 : w ≠ 0 := qc_ne_zero_of_im hwim
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwinv : ‖w‖⁻¹ ≤ C := by
    rw [inv_le_comm₀ hwn hC]; exact hw1
  set z' := z - (z + w⁻¹) / N with hz'def
  have hsub := mFun_pred_eq σ hσ hN2 hz
  rw [← hwdef, ← hz'def] at hsub
  have hzz : ‖z - z'‖ ≤ D / N := by
    have : z - z' = (z + w⁻¹) / N := by rw [hz'def]; ring
    rw [this, norm_div, Complex.norm_natCast]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    refine (norm_add_le _ _).trans ?_
    rw [norm_inv]
    linarith
  have hz'im : z.im / 2 ≤ z'.im := by
    have hn2 : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    have e : z'.im = z.im * (1 - 1 / N) + w.im / (Complex.normSq w * N) := by
      simp [hz'def, Complex.sub_im, Complex.div_im, Complex.add_im, Complex.inv_im]
      field_simp
      ring
    rw [e]
    have : 0 ≤ w.im / (Complex.normSq w * N) := by positivity
    have : z.im / 2 ≤ z.im * (1 - 1 / N) := by
      have : 1 / (N : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
      nlinarith
    linarith
  have hz'pos : 0 < z'.im := by linarith
  have hDN : D / N ≤ τ / 2 := by
    rw [div_le_iff₀ hN0]
    have : 2 * D / τ ≤ N := by nlinarith [mul_pos hD hτ]
    rw [div_le_iff₀ hτ] at this
    linarith
  have hDN' : D / N ≤ τ⁻¹ := by
    rw [div_le_iff₀ hN0]
    have h3 : D * τ ≤ N := by nlinarith [mul_pos (div_pos (mul_pos two_pos hD) hτ) hτ]
    have : D ≤ τ⁻¹ * N := by
      rw [← div_le_iff₀' hτi, div_inv_eq_mul]
      exact h3
    linarith
  have htri1 : ‖z‖ ≤ ‖z'‖ + ‖z - z'‖ := by
    calc ‖z‖ = ‖z' + (z - z')‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have htri2 : ‖z'‖ ≤ ‖z‖ + ‖z - z'‖ := by
    calc ‖z'‖ = ‖z - (z - z')‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hz'1 : τ / 2 ≤ ‖z'‖ := by linarith
  have hz'2 : ‖z'‖ ≤ (τ / 2)⁻¹ := by
    have e : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
    rw [e]
    linarith
  obtain ⟨-, hm1, -⟩ := gen_prop_m h2 hz (hτ2.trans hz1) (hz2.trans hτi2)
  obtain ⟨-, hm2, -⟩ := gen_prop_m h2 hz'pos hz'1 hz'2
  have hlip := qc_m_lip N σ hσ hz'pos hz
  have hi1 : (mFun N σ z).im ≤ C := (Complex.im_le_norm _).trans hm1
  have hi2 : (mFun N σ z').im ≤ C := (Complex.im_le_norm _).trans hm2
  have hi1' : 0 < (mFun N σ z).im := (mFun_spec N σ hσ hz).1
  have hi2' : 0 < (mFun N σ z').im := (mFun_spec N σ hσ hz'pos).1
  have hzz' : ‖z' - z‖ ≤ D / N := by rw [norm_sub_rev]; exact hzz
  have hR : ‖z' - z‖ ^ 2 * ((mFun N σ z').im * (mFun N σ z).im) ≤ (D / N) ^ 2 * (C * C) :=
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzz' 2) (mul_le_mul hi2 hi1 hi1'.le hC.le)
      (by positivity) (by positivity)
  rw [hsub]
  set d := ‖mFun N σ z' - mFun N σ z‖ with hd
  have hL : d ^ 2 * (z.im * z.im / 2) ≤ d ^ 2 * (z'.im * z.im) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  have hpos : 0 < z.im * z.im / 2 := by positivity
  have h5 : d ^ 2 * (z.im * z.im / 2) ≤ (D / N) ^ 2 * (C * C) := hL.trans (hlip.trans hR)
  have h6 : d ^ 2 ≤ (D / N) ^ 2 * (C * C) / (z.im * z.im / 2) := by
    rw [le_div_iff₀ hpos]; exact h5
  have h7 : (D / N) ^ 2 * (C * C) / (z.im * z.im / 2) ≤ (2 * C * D / (N * z.im)) ^ 2 := by
    rw [div_le_iff₀ hpos]
    have e : (2 * C * D / (N * z.im)) ^ 2 * (z.im * z.im / 2) = 2 * ((D / N) ^ 2 * (C * C)) := by
      field_simp
    rw [e]
    have : 0 ≤ (D / N) ^ 2 * (C * C) := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp (h6.trans h7)

/-! ## Boundary values of `m` off the support of `ϱ` -/

private lemma qc_im_mFun_eq (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {z : ℂ}
    (hz : 0 < z.im) :
    (mFun K σ z).im = ∫ t, z.im / ((t - z.re) ^ 2 + z.im ^ 2) ∂(varrho K σ) := by
  have := isProbabilityMeasure_varrho K σ hσ hK
  have hne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hint : Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) (varrho K σ) := by
    refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun t => ?_)
    · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable
    · rw [norm_inv]
      refine inv_anti₀ hz ?_
      have h := Complex.abs_im_le_norm ((t : ℂ) - z)
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
      exact (le_abs_self _).trans h
  have hm : mFun K σ z = ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(varrho K σ) := by
    rw [← resolventTransform_varrho K σ hσ hK hz, resolventTransform_apply]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [resolvent, Ring.inverse_eq_inv']
  rw [hm]
  have := integral_im (𝕜 := ℂ) hint
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  dsimp only
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  ring

/-- `Im m(z) ≤ Im z / d²` when the support of `ϱ` is at distance `≥ d` from `Re z`. -/
private lemma qc_im_le_of_dist (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {z : ℂ}
    (hz : 0 < z.im) {d : ℝ} (hd : 0 < d)
    (hsupp : ∀ t ∈ (varrho K σ).support, d ≤ |t - z.re|) :
    (mFun K σ z).im ≤ z.im / d ^ 2 := by
  have := isProbabilityMeasure_varrho K σ hσ hK
  rw [qc_im_mFun_eq K σ hσ hK hz]
  have hb : ∀ᵐ t ∂(varrho K σ), z.im / ((t - z.re) ^ 2 + z.im ^ 2) ≤ z.im / d ^ 2 := by
    filter_upwards [Measure.support_mem_ae (μ := varrho K σ)] with t ht
    have h1 := hsupp t ht
    have h2 : d ^ 2 ≤ (t - z.re) ^ 2 := by
      have := pow_le_pow_left₀ hd.le h1 2
      rwa [sq_abs] at this
    exact div_le_div_of_nonneg_left hz.le (by positivity) (by nlinarith)
  calc ∫ t, z.im / ((t - z.re) ^ 2 + z.im ^ 2) ∂(varrho K σ)
      ≤ ∫ _t, z.im / d ^ 2 ∂(varrho K σ) := integral_mono_ae (by
        refine Integrable.of_bound ?_ (1 / z.im) (ae_of_all _ fun t => ?_)
        · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hz]
          nlinarith [sq_nonneg (t - z.re)]) (integrable_const _) hb
    _ = z.im / d ^ 2 := by simp

/-- The path `y ↦ E + i y`, `y ↓ 0`, tends to `E` within `ℂ₊`. -/
private lemma qc_tendsto_path (E : ℝ) :
    Tendsto (fun y : ℝ => (E : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[upperHalf] (E : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun y : ℝ => (E : ℂ) + (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((E : ℂ) + 0)) := by
      have := ((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).const_add (E : ℂ)
      simpa using this
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp [upperHalf]
    exact hy

private lemma qc_tendsto_mFun_path (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {E : ℝ}
    (hE : E ≠ 0) :
    Tendsto (fun y : ℝ => mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (mExt K σ E)) :=
  (tendsto_mFun_of_ne_zero K σ hσ hE).comp (qc_tendsto_path E)

private lemma qc_path_im {E y : ℝ} : ((E : ℂ) + (y : ℂ) * Complex.I).im = y := by simp

private lemma qc_path_re {E y : ℝ} : ((E : ℂ) + (y : ℂ) * Complex.I).re = E := by simp

/-- Off the support, `m(E + i0)` is real. -/
private lemma qc_mExt_im_eq_zero (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) {d : ℝ} (hd : 0 < d) (hsupp : ∀ t ∈ (varrho K σ).support, d ≤ |t - E|) :
    (mExt K σ E).im = 0 := by
  have ht := (Complex.continuous_im.tendsto _).comp (qc_tendsto_mFun_path K σ hσ hE)
  refine le_antisymm ?_ (im_mExt_nonneg K σ hσ hE)
  have hup : Tendsto (fun y : ℝ => y / d ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => y / d ^ 2) (𝓝 0) (𝓝 (0 / d ^ 2)) :=
      (continuous_id.div_const _).tendsto 0
    rw [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto ht hup ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by rw [qc_path_im]; exact hy
  have := qc_im_le_of_dist K σ hσ hK hy' hd (by rw [qc_path_re]; exact hsupp)
  simpa [qc_path_im] using this

/-- A real boundary value `x = m(E + i0)`, `E ≠ 0`: `x ≠ 0`, `x` is not a pole, `f(x) = E`. -/
private lemma qc_real_facts (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) (him : (mExt K σ E).im = 0) :
    mExt K σ E = ((mExt K σ E).re : ℂ) ∧ (mExt K σ E).re ≠ 0 ∧
      (∀ i, 1 + σ i * (mExt K σ E).re ≠ 0) ∧ fR K σ (mExt K σ E).re = E := by
  set w := mExt K σ E with hw
  have hwx : w = (w.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hev := scPoly_eval_mExt K σ hσ hE
  rw [← hw] at hev
  have hw0 : w ≠ 0 := by
    intro h; rw [h, scPoly_eval_zero] at hev; norm_num at hev
  have hx0 : w.re ≠ 0 := by
    intro h; apply hw0; rw [hwx, h]; simp
  have hpole : ∀ i, 1 + σ i * w.re ≠ 0 := by
    intro i h
    rcases (hσ i).eq_or_lt with h0 | hpos
    · rw [← h0] at h; simp at h
    · have hs : σ i ∈ posVals σ :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hpos⟩
      have hx : w = -((σ i : ℂ))⁻¹ := by
        rw [hwx]
        have : w.re = -(σ i)⁻¹ := by field_simp; linarith
        rw [this]; push_cast; ring
      exact scPoly_eval_pole K σ hK (E : ℂ) hs (hx ▸ hev)
  have hpole' : ∀ s ∈ posVals σ, 1 + (s : ℂ) * w ≠ 0 := by
    intro s hs h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    apply hpole i
    have := congrArg Complex.re h
    rw [hwx] at this
    simp at this
    rw [hi]; linarith
  have hev2 := scPoly_eval K σ hσ (E : ℂ) hw0 hpole'
  rw [hev] at hev2
  have hprod : ∏ s ∈ posVals σ, (1 + (s : ℂ) * w) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpole'
  have hf : fC K σ w = E := by
    have := mul_eq_zero.mp hev2.symm
    rcases this with h | h
    · exact absurd h (mul_ne_zero hw0 hprod)
    · exact sub_eq_zero.mp h
  refine ⟨hwx, hx0, hpole, ?_⟩
  have := hf
  rw [hwx, fC_ofReal] at this
  exact_mod_cast this

/-- Off the support, `f'(m(E)) ≥ dist(E, supp ϱ)²`. -/
private lemma qc_fR1_ge_dist (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) {d : ℝ} (hd : 0 < d) (hsupp : ∀ t ∈ (varrho K σ).support, d ≤ |t - E|) :
    d ^ 2 ≤ fR1 K σ (mExt K σ E).re := by
  have him := qc_mExt_im_eq_zero K σ hσ hK hE hd hsupp
  obtain ⟨hwx, hx0, hpole, -⟩ := qc_real_facts K σ hσ hK hE him
  set x := (mExt K σ E).re
  set g : ℂ → ℝ := fun w => (‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * w‖ ^ 2) with hg
  have hgx : g x = fR1 K σ x := by
    simp only [hg, fR1]
    congr 1
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      have : (1 + (σ i : ℂ) * (x : ℂ)) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcont : ContinuousAt g (x : ℂ) := by
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
    refine ContinuousAt.sub ?_ ?_
    · exact ((continuous_norm.pow 2).continuousAt).inv₀
        (pow_pos (norm_pos_iff.mpr hxc) 2).ne'
    · refine tendsto_finsetSum _ fun i _ => ?_
      refine continuousAt_const.div (continuousAt_const.mul
        ((continuous_norm.comp (continuous_const.add (continuous_const.mul continuous_id))).pow 2
          |>.continuousAt)) ?_
      have h1 : (1 + (σ i : ℂ) * (x : ℂ)) ≠ 0 := by
        have : (1 + (σ i : ℂ) * (x : ℂ)) = ((1 + σ i * x : ℝ) : ℂ) := by push_cast; ring
        rw [this]; exact_mod_cast hpole i
      have : (0 : ℝ) < K := by exact_mod_cast hK
      have h2 : 0 < ‖1 + (σ i : ℂ) * (x : ℂ)‖ := norm_pos_iff.mpr h1
      positivity
  have ht : Tendsto (fun y : ℝ => g (mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I))) (𝓝[>] 0)
      (𝓝 (g x)) := by
    have := qc_tendsto_mFun_path K σ hσ hE
    rw [hwx] at this
    exact hcont.tendsto.comp this
  rw [← hgx]
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by rw [qc_path_im]; exact hy
  obtain ⟨hm, hfm⟩ := mFun_spec K σ hσ hy'
  have hi := im_fC K σ (mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I))
  rw [hfm, qc_path_im] at hi
  have hb := qc_im_le_of_dist K σ hσ hK hy' hd (by rw [qc_path_re]; exact hsupp)
  rw [qc_path_im] at hb
  change d ^ 2 ≤ (‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)⁻¹ -
    ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
  set G := (‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)⁻¹ -
    ∑ i, σ i ^ 2 / (K * ‖1 + (σ i : ℂ) * mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
  set q := (mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)).im
  have hq : y = q * G := hi
  rw [le_div_iff₀ (by positivity)] at hb
  have hd2 : 0 < d ^ 2 := by positivity
  nlinarith

/-- `ϱ` does not charge an interval of `(0, ∞)` on which `m(E + i0)` is real. -/
private lemma qc_varrho_Ioo_eq_zero (K : ℕ) (σ : Fin M → ℝ) {α β : ℝ} (hα : 0 ≤ α)
    (h : ∀ E ∈ Set.Ioo α β, (mExt K σ E).im = 0) : varrho K σ (Set.Ioo α β) = 0 := by
  have hA : MeasurableSet (Set.Ioo α β) := measurableSet_Ioo
  have h0 : (0 : ℝ) ∉ Set.Ioo α β := fun h0 => by linarith [h0.1]
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  have : ∫⁻ x in Set.Ioo α β ∩ Set.Ioi 0, ENNReal.ofReal (rhoDens K σ x) =
      ∫⁻ _x in Set.Ioo α β ∩ Set.Ioi 0, 0 :=
    setLIntegral_congr_fun (hA.inter measurableSet_Ioi) fun x hx => by
      simp only [rhoDens]
      rw [h x hx.1, zero_div, ENNReal.ofReal_zero]
  rw [this, lintegral_zero]

private lemma qc_not_mem_support_of_Ioo (K : ℕ) (σ : Fin M → ℝ) {α β E : ℝ} (hα : 0 ≤ α)
    (h : ∀ E ∈ Set.Ioo α β, (mExt K σ E).im = 0) (hE : E ∈ Set.Ioo α β) :
    E ∉ (varrho K σ).support :=
  Measure.notMem_support_iff_exists.2 ⟨_, Ioo_mem_nhds hE.1 hE.2, qc_varrho_Ioo_eq_zero K σ hα h⟩

/-- Near a point with `f' > 0`, `f` has a local inverse given by `m(· + i0)`. -/
private lemma qc_local_inv (K : ℕ) (σ : Fin M → ℝ) {y : ℝ}
    (hy : y ≠ 0) (hy' : ∀ i, 1 + σ i * y ≠ 0) (hd : 0 < fR1 K σ y) :
    ∃ r > 0, (∀ y' ∈ Set.Icc (y - r) (y + r), y' ≠ 0 ∧ (∀ i, 1 + σ i * y' ≠ 0) ∧
      0 < fR1 K σ y') ∧ StrictMonoOn (fR K σ) (Set.Icc (y - r) (y + r)) := by
  have hev : ∀ᶠ y' in 𝓝 y, y' ≠ 0 ∧ (∀ i, 1 + σ i * y' ≠ 0) ∧ 0 < fR1 K σ y' := by
    refine (eventually_ne_nhds hy).and ((?_ : ∀ᶠ y' in 𝓝 y, ∀ i, 1 + σ i * y' ≠ 0).and ?_)
    · refine Filter.eventually_all.2 fun i => ?_
      exact (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.eventually_ne
        (hy' i)
    · exact (hasDerivAt_fR1 K σ hy hy').continuousAt.eventually (lt_mem_nhds hd)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ y' ∈ Set.Icc (y - ε / 2) (y + ε / 2), y' ≠ 0 ∧ (∀ i, 1 + σ i * y' ≠ 0) ∧
      0 < fR1 K σ y' := fun y' hy'' => hball (by
    rw [Real.dist_eq]
    have : |y' - y| ≤ ε / 2 := abs_le.2 ⟨by linarith [hy''.1], by linarith [hy''.2]⟩
    linarith)
  refine ⟨ε / 2, by positivity, hgood, ?_⟩
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ fun x hx => ?_
  · intro x hx
    obtain ⟨h0, h1, -⟩ := hgood x hx
    exact (hasDerivAt_fR K σ h0 h1).continuousAt.continuousWithinAt
  · have hx' := interior_subset hx
    obtain ⟨h0, h1, h2⟩ := hgood x hx'
    rw [(hasDerivAt_fR K σ h0 h1).deriv]
    exact h2

/-- `f' > 0` at `y`: then `m(f(y) + i0) = y`, and `f(y) > 0` is not in the support of `ϱ`. -/
private lemma qc_not_mem_support (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {y : ℝ}
    (hy : y ≠ 0) (hy' : ∀ i, 1 + σ i * y ≠ 0) (hd : 0 < fR1 K σ y) (hf : 0 < fR K σ y) :
    fR K σ y ∉ (varrho K σ).support := by
  obtain ⟨r, hr, hgood, hmono⟩ := qc_local_inv K σ hy hy' hd
  have hlo : fR K σ (y - r) < fR K σ y :=
    hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hhi : fR K σ y < fR K σ (y + r) :=
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hcont : ContinuousOn (fR K σ) (Set.Icc (y - r) (y + r)) := fun x hx => by
    obtain ⟨h0, h1, -⟩ := hgood x hx
    exact (hasDerivAt_fR K σ h0 h1).continuousAt.continuousWithinAt
  refine qc_not_mem_support_of_Ioo K σ (le_max_left 0 (fR K σ (y - r)))
    (β := fR K σ (y + r)) (fun E hE => ?_) ⟨max_lt hf hlo, hhi⟩
  have hE0 : 0 < E := lt_of_le_of_lt (le_max_left _ _) hE.1
  obtain ⟨y', hy'm, hy'E⟩ := intermediate_value_Icc (show y - r ≤ y + r by linarith) hcont
    ⟨(le_max_right _ _).trans hE.1.le, hE.2.le⟩
  obtain ⟨h0, h1, h2⟩ := hgood y' hy'm
  have := mExt_fR_of_pos K σ hσ hK h0 h1 (by rw [hy'E]; exact hE0.ne') h2
  rw [hy'E] at this
  rw [this]
  simp

/-! ## The critical points `x_k` and the edges `a_k` -/

private lemma qc_pos_of_mem {σ : Fin M → ℝ} {s : ℝ} (hs : s ∈ posVals σ) : 0 < s :=
  (Finset.mem_filter.mp hs).2

private lemma qc_mem_posVals {σ : Fin M → ℝ} {i : Fin M} (hi : 0 < σ i) : σ i ∈ posVals σ :=
  Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩

private lemma qc_weight_pos (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) {s : ℝ}
    (hs : s ∈ posVals σ) : 0 < weight K σ s := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  unfold weight
  have hc : 0 < (Finset.univ.filter fun j => σ j = s).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  positivity

private lemma qc_nonpole_all {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hx : ∀ s ∈ posVals σ, 1 + s * x ≠ 0) : ∀ i, 1 + σ i * x ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact hx (σ i) (qc_mem_posVals hpos)

private lemma qc_critPoly_ne_zero (K : ℕ) (σ : Fin M → ℝ) : critPoly K σ ≠ 0 := by
  intro h
  have := critPoly_eval_zero K σ
  rw [h] at this
  simp at this

private lemma qc_critPoly_pole (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) {u : ℝ}
    (hu : u ∈ posVals σ) : (critPoly K σ).eval (-u⁻¹) ≠ 0 := by
  have hu0 := qc_pos_of_mem hu
  have hP : ∏ t ∈ posVals σ, (1 + t * (-u⁻¹)) ^ 2 = 0 := by
    refine Finset.prod_eq_zero hu ?_
    field_simp
    ring
  have hsum : ∑ t ∈ posVals σ, weight K σ t * t ^ 2 *
        ∏ s' ∈ (posVals σ).erase t, (1 + s' * (-u⁻¹)) ^ 2 =
      weight K σ u * u ^ 2 * ∏ s' ∈ (posVals σ).erase u, (1 + s' * (-u⁻¹)) ^ 2 := by
    refine Finset.sum_eq_single u (fun t ht htu => ?_) (fun h => absurd hu h)
    have hmem : u ∈ (posVals σ).erase t := Finset.mem_erase.mpr ⟨htu.symm, hu⟩
    rw [Finset.prod_eq_zero hmem (by field_simp; ring), mul_zero]
  have hev : (critPoly K σ).eval (-u⁻¹) = ∏ t ∈ posVals σ, (1 + t * (-u⁻¹)) ^ 2 -
      (-u⁻¹) ^ 2 * ∑ t ∈ posVals σ, weight K σ t * t ^ 2 *
        ∏ s' ∈ (posVals σ).erase t, (1 + s' * (-u⁻¹)) ^ 2 := by
    simp only [critPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_finsetSum]
  rw [hev, hP, hsum, zero_sub, neg_ne_zero]
  refine mul_ne_zero (pow_ne_zero 2 (neg_ne_zero.mpr (inv_ne_zero hu0.ne')))
    (mul_ne_zero (mul_ne_zero (qc_weight_pos K σ hK hu).ne' (pow_ne_zero 2 hu0.ne')) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  have htu : t ≠ u := (Finset.mem_erase.mp ht).1
  have : 1 + t * (-u⁻¹) = (u - t) / u := by field_simp; ring
  rw [this]
  exact pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr htu.symm) hu0.ne')

/-- A point of `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)`: in the inner region, not a pole, critical. -/
private lemma qc_mem_innerCrit (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    {x : ℝ} (hx : x ∈ innerCrit K σ) :
    InInner σ x ∧ (∀ i, 1 + σ i * x ≠ 0) ∧ fR1 K σ x = 0 := by
  unfold innerCrit at hx
  rw [Multiset.mem_filter, Polynomial.mem_roots (qc_critPoly_ne_zero K σ)] at hx
  obtain ⟨hroot, hin⟩ := hx
  have h0 : (critPoly K σ).eval x = 0 := hroot
  have hnp : ∀ u ∈ posVals σ, 1 + u * x ≠ 0 := by
    intro u hu h
    have hu0 := qc_pos_of_mem hu
    have hx' : x = -u⁻¹ := by
      field_simp
      linear_combination h
    rw [hx'] at h0
    exact qc_critPoly_pole K σ hK hu h0
  refine ⟨hin, qc_nonpole_all hσ hnp, ?_⟩
  rw [critPoly_eval K σ hσ hin.1.ne (qc_nonpole_all hσ hnp)] at h0
  have hpre : x ^ 2 * ∏ s ∈ posVals σ, (1 + s * x) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hin.1.ne)
      (Finset.prod_ne_zero_iff.mpr fun s hs => pow_ne_zero 2 (hnp s hs))
  exact (mul_eq_zero.mp h0).resolve_left hpre

/-- A critical point in the inner region, not a pole, belongs to `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)`. -/
private lemma qc_innerCrit_of (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {x : ℝ}
    (hin : InInner σ x) (hnp : ∀ i, 1 + σ i * x ≠ 0) (h1 : fR1 K σ x = 0) :
    x ∈ innerCrit K σ := by
  unfold innerCrit
  rw [Multiset.mem_filter, Polynomial.mem_roots (qc_critPoly_ne_zero K σ)]
  refine ⟨?_, hin⟩
  show (critPoly K σ).eval x = 0
  rw [critPoly_eval K σ hσ hin.1.ne hnp, h1, mul_zero]

/-- In a list sorted in decreasing order, the entries `> y` form an initial segment. -/
private lemma qc_list_prefix (y : ℝ) : ∀ (L : List ℝ), L.Pairwise (fun a b => b ≤ a) →
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
      have ih := qc_list_prefix y L hpw.2 j hj
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

private lemma qc_sort_spec (m : Multiset ℝ) {i : ℕ} (hi : i < Multiset.card m) :
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
  · rw [qc_list_prefix y _ hpw i hi', ← Multiset.countP_eq_card_filter,
      ← Multiset.coe_countP, Multiset.coe_reverse, Multiset.sort_eq]

/-- `x_k ∈ 𝒞` for `k < 2p`, and `y < x_k` iff at least `k` points of `𝒞` lie in `(y, ∞)`. -/
private lemma qc_xCrit_spec (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands K σ) :
    xCrit K σ k ∈ innerCrit K σ ∧
      ∀ y, (y < xCrit K σ k ↔ k ≤ Multiset.card ((innerCrit K σ).filter (fun x => y < x))) := by
  have hc := (card_innerCrit K σ hσ hK hS).1
  have hx : xCrit K σ k = ((innerCrit K σ).sort (· ≤ ·)).reverse.getD (k - 1) 0 := by
    unfold xCrit
    rw [ite_eq_right (by omega)]
  obtain ⟨hmem, hspec⟩ := qc_sort_spec (innerCrit K σ) (i := k - 1) (by omega)
  rw [hx]
  refine ⟨hmem, fun y => ?_⟩
  rw [hspec y]
  omega

/-- `x_1 ≥ x_2 ≥ ⋯ ≥ x_{2p−1}`. -/
private lemma qc_xCrit_anti (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hk : k < 2 * numBands K σ) : xCrit K σ k ≤ xCrit K σ j := by
  by_contra hlt
  push Not at hlt
  have h1 := ((qc_xCrit_spec K σ hσ hK hS (hj.trans hjk) hk).2 (xCrit K σ j)).1 hlt
  have h2 := (qc_xCrit_spec K σ hσ hK hS hj (lt_of_le_of_lt hjk hk)).2 (xCrit K σ j)
  have : ¬ (xCrit K σ j < xCrit K σ j) := lt_irrefl _
  rw [h2] at this
  omega

/-- `x_1 ∈ I_1`: `1 + s x_1 > 0` for every positive value `s`. -/
private lemma qc_xCrit_one (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) : ∀ s ∈ posVals σ, 0 < 1 + s * xCrit K σ 1 := by
  have hp := card_innerCrit K σ hσ hK hS
  have h1 := card_innerCrit_I1 K σ hσ hK hS
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (innerCrit K σ).filter (fun x => ∀ s ∈ posVals σ, 0 < 1 + s * x) :=
    Multiset.card_pos_iff_exists_mem.mp (by omega)
  rw [Multiset.mem_filter] at hy
  have hspec := (qc_xCrit_spec K σ hσ hK hS le_rfl (by omega)).2
  have hyx : y ≤ xCrit K σ 1 := by
    by_contra hlt
    push Not at hlt
    have := (hspec (xCrit K σ 1)).1
    have h0 : 1 ≤ Multiset.card ((innerCrit K σ).filter (fun x => xCrit K σ 1 < x)) :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨y, Multiset.mem_filter.mpr ⟨hy.1, hlt⟩⟩
    exact lt_irrefl _ ((hspec _).2 h0)
  intro s hs
  have := hy.2 s hs
  have hs0 := qc_pos_of_mem hs
  nlinarith

/-- `a_{2p} ≤ ⋯ ≤ a_1`. -/
private lemma qc_edge_anti (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hk : k ≤ 2 * numBands K σ) : edgeVal K σ k ≤ edgeVal K σ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := edgeVal_succ_le K σ hσ hK hS (k := j + d) (by omega) (by omega)
    rw [← add_assoc]
    exact h2.trans h1

/-! ## The support of `ϱ` and its gaps -/

private lemma qc_measure_null_of_subset (K : ℕ) (σ : Fin M → ℝ) {S : Set ℝ}
    (hS : ∀ t ∈ S, t ∉ (varrho K σ).support) : varrho K σ S = 0 :=
  measure_mono_null (fun t ht => hS t ht) Measure.measure_compl_support

private lemma qc_varrho_singleton (K : ℕ) (σ : Fin M → ℝ) {x : ℝ} (hx : 0 < x) :
    varrho K σ {x} = 0 := by
  have hA : MeasurableSet ({x} : Set ℝ) := measurableSet_singleton x
  have hsub : ({x} : Set ℝ) ⊆ Set.Ioi 0 := fun y hy => by
    rw [Set.mem_singleton_iff.mp hy]; exact hx
  have h0 : (0 : ℝ) ∉ ({x} : Set ℝ) := fun h => hx.ne (Set.mem_singleton_iff.mp h)
  rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    Set.indicator_of_notMem h0, smul_zero, zero_add, withDensity_apply _ hA,
    Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

/-- The support lies in `[0, a_1]`. -/
private lemma qc_supp_mem_Icc (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {t : ℝ} (ht : t ∈ (varrho K σ).support) :
    0 ≤ t ∧ t ≤ edgeVal K σ 1 := by
  by_contra hno
  have hopen : IsOpen (Set.Icc 0 (edgeVal K σ 1))ᶜ := isClosed_Icc.isOpen_compl
  exact (Measure.notMem_support_iff_exists.2 ⟨_, hopen.mem_nhds hno,
    varrho_compl_Icc_edgeVal K σ hσ hK hS⟩) ht

/-- A support point `u > 0` lies in a band. -/
private lemma qc_supp_band (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {u : ℝ} (hu : 0 < u) (hs : u ∈ (varrho K σ).support) :
    ∃ j, 1 ≤ j ∧ j ≤ numBands K σ ∧ edgeVal K σ (2 * j) ≤ u ∧ u ≤ edgeVal K σ (2 * j - 1) := by
  obtain ⟨j, h1, h2, h3⟩ := (mem_support_varrho_iff K σ hσ hK hS hu).1 hs
  exact ⟨j, h1, h2, h3.1, h3.2⟩

private lemma qc_edge_nonneg {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * numBands K σ) :
    0 ≤ edgeVal K σ k ∧ edgeVal K σ k ≤ 2 * τ⁻¹ * (1 + τ⁻¹) :=
  edgeVal_mem_Icc K σ h.nonneg hK (qc_posVals_nonempty h) h.pos h.phi_lower h.phi_upper
    h.bound_Sigma hk1 hk

/-- The gap between the bands `g + 1` and `g`. -/
private lemma qc_supp_gap {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K)
    {g : ℕ} (hg1 : 1 ≤ g) (hg : g < numBands K σ) :
    ∀ u ∈ (varrho K σ).support, u ≤ edgeVal K σ (2 * g + 1) ∨ edgeVal K σ (2 * g) ≤ u := by
  intro u hu
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  rcases le_or_gt u 0 with h0 | h0
  · exact Or.inl (h0.trans (qc_edge_nonneg h hK (by omega) (by omega)).1)
  obtain ⟨j, hj1, hj, hl, hr⟩ := qc_supp_band K σ hσ hK hS h0 hu
  rcases le_or_gt j g with hjg | hjg
  · exact Or.inr ((qc_edge_anti K σ hσ hK hS (by omega) (by omega) (by omega)).trans hl)
  · exact Or.inl (hr.trans (qc_edge_anti K σ hσ hK hS (by omega) (by omega) (by omega)))

private lemma qc_supp_bottom {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) : ∀ u ∈ (varrho K σ).support, u ≤ 0 ∨ edgeVal K σ (2 * numBands K σ) ≤ u := by
  intro u hu
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  rcases le_or_gt u 0 with h0 | h0
  · exact Or.inl h0
  obtain ⟨j, hj1, hj, hl, hr⟩ := qc_supp_band K σ hσ hK hS h0 hu
  exact Or.inr ((qc_edge_anti K σ hσ hK hS (by omega) (by omega) le_rfl).trans hl)

/-- `m(t + i0)` is real at a point `t` of a gap `(α, β)` of the support. -/
private lemma qc_im_zero_gap (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {α β t : ℝ}
    (hα : 0 ≤ α) (ht : t ∈ Set.Ioo α β)
    (hsupp : ∀ u ∈ (varrho K σ).support, u ≤ α ∨ β ≤ u) : (mExt K σ t).im = 0 := by
  refine qc_mExt_im_eq_zero K σ hσ hK (by linarith [ht.1]) (d := min (t - α) (β - t))
    (lt_min (by linarith [ht.1]) (by linarith [ht.2])) fun u hu => ?_
  rcases hsupp u hu with h | h
  · rw [abs_of_nonpos (by linarith [ht.1])]
    exact (min_le_left _ _).trans (by linarith)
  · rw [abs_of_nonneg (by linarith [ht.2])]
    exact (min_le_right _ _).trans (by linarith)

/-- `m(t + i0)` is real above the support. -/
private lemma qc_im_zero_top (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {α t : ℝ}
    (hα : 0 ≤ α) (ht : α < t) (hsupp : ∀ u ∈ (varrho K σ).support, u ≤ α) :
    (mExt K σ t).im = 0 :=
  qc_im_zero_gap K σ hσ hK (β := t + 1) hα ⟨ht, by linarith⟩ fun u hu => Or.inl (hsupp u hu)

/-- Off the support, `m(E + i0)` is real. -/
private lemma qc_im_zero_of_not_mem (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E : ℝ}
    (hE : E ≠ 0) (hns : E ∉ (varrho K σ).support) : (mExt K σ E).im = 0 := by
  have ho : IsOpen (varrho K σ).supportᶜ := Measure.isClosed_support.isOpen_compl
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.1 ho E hns
  refine qc_mExt_im_eq_zero K σ hσ hK hE (d := d) hd fun u hu => ?_
  by_contra hlt
  push Not at hlt
  have : u ∈ Metric.ball E d := by rw [Metric.mem_ball, Real.dist_eq]; exact hlt
  exact hball this hu

/-- `t ↦ m(t + i0)` is continuous on `[a, b] ⊂ (0, ∞)`. -/
private lemma qc_cont_mExt (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => mExt K σ t) (Set.Icc a b) := by
  refine (continuousOn_mExt K σ hσ).comp Complex.continuous_ofReal.continuousOn fun t ht => ?_
  right
  refine ⟨by simp, ?_⟩
  have : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by linarith [ht.1])
  exact this

/-- A continuous function without zeros keeps its sign on an interval. -/
private lemma qc_sign_const {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hu : ContinuousOn u (Set.Icc a b))
    (h0 : ∀ t ∈ Set.Icc a b, u t ≠ 0) : (0 < u a ↔ 0 < u b) := by
  constructor
  · intro ha
    by_contra hb
    push Not at hb
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hu ⟨hb, ha.le⟩
    exact h0 c hc hc0
  · intro hb
    by_contra ha
    push Not at ha
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hu ⟨ha, hb.le⟩
    exact h0 c hc hc0

/-- The pole count `#{i : 1 + σ_i y < 0}`. -/
private def qcP (σ : Fin M → ℝ) (y : ℝ) : ℕ := (Finset.univ.filter fun i => 1 + σ i * y < 0).card

/-- If `m(· + i0)` is real on `[a, b] ⊂ (0, ∞)`, its values at `a` and `b` have the same sign and
the same pole count. -/
private lemma qc_real_on (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hre : ∀ t ∈ Set.Icc a b, (mExt K σ t).im = 0) :
    (0 < (mExt K σ a).re ↔ 0 < (mExt K σ b).re) ∧
      qcP σ (mExt K σ a).re = qcP σ (mExt K σ b).re := by
  have hc : ContinuousOn (fun t : ℝ => (mExt K σ t).re) (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn (qc_cont_mExt K σ hσ ha)
  have hfacts : ∀ t ∈ Set.Icc a b, (mExt K σ t).re ≠ 0 ∧ ∀ i, 1 + σ i * (mExt K σ t).re ≠ 0 :=
    fun t ht => by
      obtain ⟨-, h1, h2, -⟩ := qc_real_facts K σ hσ hK (by linarith [ht.1]) (hre t ht)
      exact ⟨h1, h2⟩
  refine ⟨qc_sign_const hab hc fun t ht => (hfacts t ht).1, ?_⟩
  unfold qcP
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  have hci : ContinuousOn (fun t : ℝ => 1 + σ i * (mExt K σ t).re) (Set.Icc a b) :=
    continuousOn_const.add (continuousOn_const.mul hc)
  have := qc_sign_const hab hci fun t ht => (hfacts t ht).2 i
  have ha' := (hfacts a ⟨le_rfl, hab⟩).2 i
  have hb' := (hfacts b ⟨hab, le_rfl⟩).2 i
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact absurd (this.2 (lt_of_le_of_ne h' (Ne.symm hb'))) (not_lt.2 h.le)
  · intro h
    by_contra h'
    push Not at h'
    exact absurd (this.1 (lt_of_le_of_ne h' (Ne.symm ha'))) (not_lt.2 h.le)

/-! ## The count `n(E)` in a gap: `n(E) = #{i : 1 + σ_i m(E + i0) < 0}` -/

/-- `x_k = m(a_k + i0)` is real and nonzero, and not a pole, for an edge with finite `x_k`. -/
private lemma qc_edge_real (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * numBands K σ)
    (hfin : ¬ (k = 2 * numBands K σ ∧ yEdge K σ = 0)) :
    (mExt K σ (edgeVal K σ k)).im = 0 ∧ (mExt K σ (edgeVal K σ k)).re = xCrit K σ k := by
  rw [mExt_edgeVal K σ hσ hK hS hk1 hk hfin]
  simp

private lemma qc_inner_fin {K : ℕ} {σ : Fin M → ℝ} {k : ℕ} (hk : k < 2 * numBands K σ) :
    ¬ (k = 2 * numBands K σ ∧ yEdge K σ = 0) := fun h => by omega

private lemma qc_edge_pos {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * numBands K σ) : 0 < edgeVal K σ k := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hp := card_innerCrit K σ hσ hK hS
  have h1 := edgeVal_band_lt K σ hσ hK hS (k := numBands K σ) hp.2 le_rfl
  have h2 := qc_edge_anti K σ hσ hK hS hk1 (show k ≤ 2 * numBands K σ - 1 by omega) (by omega)
  have h3 := (qc_edge_nonneg h hK (k := 2 * numBands K σ) (by omega) le_rfl).1
  linarith

private lemma qc_FChart1_zero (K : ℕ) (σ : Fin M → ℝ) : FChart1 K σ 0 = massRatio K σ - 1 := by
  rw [← sum_weight K σ, FChart1]
  have : ∑ s ∈ posVals σ, weight K σ s * s ^ 2 / (0 + s) ^ 2 =
      ∑ s ∈ posVals σ, weight K σ s := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have := (qc_pos_of_mem hs).ne'
    rw [zero_add]
    field_simp
  rw [this]
  ring

private lemma qc_FChart1_anti (K : ℕ) (σ : Fin M → ℝ) {y₁ y₂ : ℝ} (h1 : InChart σ y₁)
    (h12 : y₁ ≤ y₂) : FChart1 K σ y₂ ≤ FChart1 K σ y₁ := by
  unfold FChart1
  have hw : ∀ s, 0 ≤ weight K σ s := fun s => by unfold weight; positivity
  have : ∑ s ∈ posVals σ, weight K σ s * s ^ 2 / (y₂ + s) ^ 2 ≤
      ∑ s ∈ posVals σ, weight K σ s * s ^ 2 / (y₁ + s) ^ 2 := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs1 := h1 s hs
    exact div_le_div_of_nonneg_left (mul_nonneg (hw s) (sq_nonneg s)) (pow_pos hs1 2)
      (pow_le_pow_left₀ hs1.le (by linarith) 2)
  linarith

/-- Measures of half-lines: `ϱ([a, ∞)) = ϱ([a, b]) + ϱ((b, ∞))`. -/
private lemma qc_Ici_split (K : ℕ) (σ : Fin M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    varrho K σ (Set.Ici a) = varrho K σ (Set.Icc a b) + varrho K σ (Set.Ioi b) := by
  rw [← measure_union _ measurableSet_Ioi]
  · rw [Set.Icc_union_Ioi_eq_Ici hab]
  · rw [Set.disjoint_left]
    intro z hz1 hz2
    exact absurd hz1.2 (not_le.mpr hz2)

/-- Across a gap `(a, b)` with `b > 0`: `ϱ((a, ∞)) = ϱ([b, ∞))`. -/
private lemma qc_Ioi_gap (K : ℕ) (σ : Fin M → ℝ) {a b : ℝ} (hab : a ≤ b) (hb : 0 < b)
    (hgap : ∀ t ∈ Set.Ioo a b, t ∉ (varrho K σ).support) :
    varrho K σ (Set.Ioi a) = varrho K σ (Set.Ici b) := by
  have h0 := qc_measure_null_of_subset K σ hgap
  refine le_antisymm ?_ ?_
  · calc varrho K σ (Set.Ioi a) ≤ varrho K σ (Set.Ioo a b ∪ Set.Ici b) :=
          measure_mono fun t ht => by
            rcases lt_or_ge t b with h | h
            · exact Or.inl ⟨ht, h⟩
            · exact Or.inr h
      _ ≤ varrho K σ (Set.Ioo a b) + varrho K σ (Set.Ici b) := measure_union_le _ _
      _ = varrho K σ (Set.Ici b) := by rw [h0, zero_add]
  · calc varrho K σ (Set.Ici b) ≤ varrho K σ (Set.Ioi a ∪ {b}) :=
          measure_mono fun t ht => by
            rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with h | h
            · exact Or.inr h.symm
            · exact Or.inl (lt_of_le_of_lt hab h)
      _ ≤ varrho K σ (Set.Ioi a) + varrho K σ {b} := measure_union_le _ _
      _ = varrho K σ (Set.Ioi a) := by rw [qc_varrho_singleton K σ hb, add_zero]

/-- `K ϱ([a_{2k}, ∞)) = N_1 + ⋯ + N_k` for `1 ≤ k ≤ p`. -/
private lemma qc_Ici_bands {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) :
    ∀ k, 1 ≤ k → k ≤ numBands K σ →
      (K : ℝ) * (varrho K σ (Set.Ici (edgeVal K σ (2 * k)))).toReal =
        ∑ l ∈ Finset.Icc 1 k, bandCount K σ l := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have := isProbabilityMeasure_varrho K σ hσ hK
  intro k hk1 hk
  induction k with
  | zero => omega
  | succ k ih =>
    have hband := edgeVal_band_lt K σ hσ hK hS (k := k + 1) (by omega) hk
    rw [qc_Ici_split K σ hband.le, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      mul_add, Finset.sum_Icc_succ_top (by omega)]
    have e1 : (K : ℝ) * (varrho K σ (Set.Icc (edgeVal K σ (2 * (k + 1)))
        (edgeVal K σ (2 * (k + 1) - 1)))).toReal = bandCount K σ (k + 1) := rfl
    rw [e1]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have : varrho K σ (Set.Ioi (edgeVal K σ (2 * (0 + 1) - 1))) = 0 := by
        refine measure_mono_null (fun t ht => ?_) (varrho_compl_Icc_edgeVal K σ hσ hK hS)
        intro hm
        exact absurd hm.2 (not_le.mpr (by simpa using ht))
      simp [this]
    · have hgap : ∀ t ∈ Set.Ioo (edgeVal K σ (2 * (k + 1) - 1)) (edgeVal K σ (2 * k)),
          t ∉ (varrho K σ).support := by
        intro t ht hs
        have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [e] at ht
        rcases qc_supp_gap h hK (g := k) hk0 (by omega) t hs with h' | h'
        · linarith [ht.1]
        · linarith [ht.2]
      have hle : edgeVal K σ (2 * (k + 1) - 1) ≤ edgeVal K σ (2 * k) :=
        qc_edge_anti K σ hσ hK hS (by omega) (by omega) (by omega)
      rw [qc_Ioi_gap K σ hle (qc_edge_pos h hK (by omega) (by omega)) hgap, ih hk0 (by omega)]
      ring

/-- `N_k = #{i : 1 + σ_i x_{2k} < 0} − #{i : 1 + σ_i x_{2k−1} < 0}` for `k < p`. -/
private lemma qc_bandCount_P (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < numBands K σ) :
    bandCount K σ k = (qcP σ (xCrit K σ (2 * k)) : ℝ) - qcP σ (xCrit K σ (2 * k - 1)) := by
  rw [bandCount_eq_card K σ hσ hK hS hk1 hk]
  obtain ⟨hm1, -⟩ := qc_xCrit_spec K σ hσ hK hS (k := 2 * k) (by omega) (by omega)
  obtain ⟨hm2, -⟩ := qc_xCrit_spec K σ hσ hK hS (k := 2 * k - 1) (by omega) (by omega)
  obtain ⟨hin1, hnp1, -⟩ := qc_mem_innerCrit K σ hσ hK hm1
  obtain ⟨hin2, hnp2, -⟩ := qc_mem_innerCrit K σ hσ hK hm2
  have hle := qc_xCrit_anti K σ hσ hK hS (j := 2 * k - 1) (k := 2 * k) (by omega) (by omega)
    (by omega)
  set x := xCrit K σ (2 * k)
  set x' := xCrit K σ (2 * k - 1)
  have hsub : (Finset.univ.filter fun i => 1 + σ i * x' < 0) ⊆
      (Finset.univ.filter fun i => 1 + σ i * x < 0) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    nlinarith [hσ i]
  have hset : (Finset.univ.filter fun j => x ≤ -(σ j)⁻¹ ∧ -(σ j)⁻¹ ≤ x') =
      (Finset.univ.filter fun i => 1 + σ i * x < 0) \
        (Finset.univ.filter fun i => 1 + σ i * x' < 0) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_lt]
    rcases (hσ j).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [_root_.inv_zero, zero_mul, add_zero, neg_zero]
      constructor
      · rintro ⟨-, h'⟩; linarith [hin2.1]
      · rintro ⟨h', -⟩; linarith
    · have e1 : x ≤ -(σ j)⁻¹ ↔ 1 + σ j * x < 0 := by
        constructor
        · intro h'
          have := mul_le_mul_of_nonneg_left h' hpos.le
          rw [mul_neg, mul_inv_cancel₀ hpos.ne'] at this
          exact lt_of_le_of_ne (by linarith) (hnp1 j)
        · intro h'
          have : σ j * x ≤ σ j * -(σ j)⁻¹ := by
            rw [mul_neg, mul_inv_cancel₀ hpos.ne']; linarith
          exact le_of_mul_le_mul_left this hpos
      have e2 : -(σ j)⁻¹ ≤ x' ↔ 0 ≤ 1 + σ j * x' := by
        constructor
        · intro h'
          have := mul_le_mul_of_nonneg_left h' hpos.le
          rw [mul_neg, mul_inv_cancel₀ hpos.ne'] at this
          linarith
        · intro h'
          have : σ j * -(σ j)⁻¹ ≤ σ j * x' := by
            rw [mul_neg, mul_inv_cancel₀ hpos.ne']; linarith
          exact le_of_mul_le_mul_left this hpos
      rw [e1, e2]
  rw [hset, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rfl

/-- `#{i : 1 + σ_i x_1 < 0} = 0`. -/
private lemma qc_P_one (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) : qcP σ (xCrit K σ 1) = 0 := by
  unfold qcP
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact not_lt.mpr (qc_xCrit_one K σ hσ hK hS (σ i) (qc_mem_posVals hpos)).le

/-- Across the gap `g`: the pole counts at `x_{2g+1}` and `x_{2g}` agree. -/
private lemma qc_P_gap {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ) (hK : 0 < K)
    {g : ℕ} (hg1 : 1 ≤ g) (hg : g < numBands K σ) :
    qcP σ (xCrit K σ (2 * g + 1)) = qcP σ (xCrit K σ (2 * g)) := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hle := qc_edge_anti K σ hσ hK hS (j := 2 * g) (k := 2 * g + 1) (by omega) (by omega)
    (by omega)
  have hpos := qc_edge_pos h hK (k := 2 * g + 1) (by omega) (by omega)
  obtain ⟨hi1, hr1⟩ := qc_edge_real K σ hσ hK hS (k := 2 * g + 1) (by omega) (by omega)
    (qc_inner_fin (by omega))
  obtain ⟨hi2, hr2⟩ := qc_edge_real K σ hσ hK hS (k := 2 * g) (by omega) (by omega)
    (qc_inner_fin (by omega))
  have hre : ∀ t ∈ Set.Icc (edgeVal K σ (2 * g + 1)) (edgeVal K σ (2 * g)),
      (mExt K σ t).im = 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · rw [← h1]; exact hi1
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · rw [h2]; exact hi2
    exact qc_im_zero_gap K σ hσ hK hpos.le ⟨h1, h2⟩ (qc_supp_gap h hK hg1 hg)
  have := (qc_real_on K σ hσ hK hpos hle hre).2
  rwa [hr1, hr2] at this

/-- `N_1 + ⋯ + N_k = #{i : 1 + σ_i x_{2k} < 0}` for `1 ≤ k < p`. -/
private lemma qc_sum_P {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ) (hK : 0 < K) :
    ∀ k, 1 ≤ k → k < numBands K σ →
      ∑ l ∈ Finset.Icc 1 k, bandCount K σ l = qcP σ (xCrit K σ (2 * k)) := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  intro k hk1 hk
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), qc_bandCount_P K σ hσ hK hS (by omega) hk]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp [qc_P_one K σ hσ hK hS]
    · rw [ih hk0 (by omega)]
      have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e, qc_P_gap h hK hk0 (by omega)]
      ring

/-- The position of a point `E > 0` off the support: above `a_1`, in a gap, or below `a_{2p}`. -/
private lemma qc_gap_cases {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K)
    {E : ℝ} (hE : 0 < E) (hns : E ∉ (varrho K σ).support) :
    edgeVal K σ 1 < E ∨
      (∃ g, 1 ≤ g ∧ g < numBands K σ ∧ edgeVal K σ (2 * g + 1) < E ∧ E < edgeVal K σ (2 * g)) ∨
      E < edgeVal K σ (2 * numBands K σ) := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hp := card_innerCrit K σ hσ hK hS
  have hnb : ∀ k, 1 ≤ k → k ≤ numBands K σ →
      ¬ (edgeVal K σ (2 * k) ≤ E ∧ E ≤ edgeVal K σ (2 * k - 1)) := by
    intro k hk1 hk hm
    exact hns ((mem_support_varrho_iff K σ hσ hK hS hE).2 ⟨k, hk1, hk, hm⟩)
  by_cases hex : ∃ k, 1 ≤ k ∧ k ≤ numBands K σ ∧ edgeVal K σ (2 * k) ≤ E
  · let k₁ := Nat.find hex
    have hk₁ : 1 ≤ k₁ ∧ k₁ ≤ numBands K σ ∧ edgeVal K σ (2 * k₁) ≤ E := Nat.find_spec hex
    have hup : edgeVal K σ (2 * k₁ - 1) < E := by
      by_contra hc
      exact hnb k₁ hk₁.1 hk₁.2.1 ⟨hk₁.2.2, not_lt.mp hc⟩
    rcases Nat.eq_or_lt_of_le hk₁.1 with h1 | h1
    · left
      rw [← h1] at hup
      simpa using hup
    · right; left
      have hmin := Nat.find_min hex (show k₁ - 1 < k₁ by omega)
      refine ⟨k₁ - 1, by omega, by omega, ?_, ?_⟩
      · have e : 2 * (k₁ - 1) + 1 = 2 * k₁ - 1 := by omega
        rw [e]; exact hup
      · by_contra hc
        exact hmin ⟨by omega, by omega, not_lt.mp hc⟩
  · right; right
    push Not at hex
    exact hex _ hp.2 le_rfl

/-- Below the support, `ϱ((−∞, E)) = ϱ({0})`. -/
private lemma qc_Iio_bottom {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K)
    {E : ℝ} (hE : 0 < E) (h3 : E < edgeVal K σ (2 * numBands K σ)) :
    varrho K σ (Set.Iio E) = varrho K σ {0} := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  refine le_antisymm ?_ (measure_mono (by simpa using hE))
  calc varrho K σ (Set.Iio E) ≤ varrho K σ ({0} ∪ (Set.Iio E \ {0})) :=
        measure_mono (by intro t ht; by_cases h0 : t = 0 <;> simp_all)
    _ ≤ varrho K σ {0} + varrho K σ (Set.Iio E \ {0}) := measure_union_le _ _
    _ = varrho K σ {0} := by
        rw [qc_measure_null_of_subset K σ (S := Set.Iio E \ {0}) ?_, add_zero]
        intro t ht hs
        rcases qc_supp_bottom h hK t hs with h' | h'
        · have := (qc_supp_mem_Icc K σ hσ hK hS hs).1
          exact ht.2 (le_antisymm h' this)
        · linarith [Set.mem_Iio.mp ht.1]

/-- Off the support at `E > 0`, with `x = m(E + i0) < 0`: `n(E) = #{i : 1 + σ_i x < 0}`, the
number of poles `−1/σ_i` above `x`. -/
private lemma qc_count {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ) (hK : 0 < K)
    {E : ℝ} (hE : 0 < E) (hns : E ∉ (varrho K σ).support) (hneg : (mExt K σ E).re < 0) :
    nClass K σ E = qcP σ (mExt K σ E).re := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hp := card_innerCrit K σ hσ hK hS
  have := isProbabilityMeasure_varrho K σ hσ hK
  rcases qc_gap_cases h hK hE hns with h1 | ⟨g, hg1, hg, hgl, hgr⟩ | h3
  · -- above `a_1`
    have hn : nClass K σ E = 0 := by
      unfold nClass
      have : varrho K σ (Set.Ici E) = 0 := by
        refine measure_mono_null (t := (Set.Icc 0 (edgeVal K σ 1))ᶜ) (fun t ht hm => ?_)
          (varrho_compl_Icc_edgeVal K σ hσ hK hS)
        exact absurd hm.2 (not_le.mpr (lt_of_lt_of_le h1 ht))
      simp [this]
    have hpos := qc_edge_pos h hK (k := 1) le_rfl (by omega)
    obtain ⟨hi1, hr1⟩ := qc_edge_real K σ hσ hK hS (k := 1) le_rfl (by omega)
      (qc_inner_fin (by omega))
    have hre : ∀ t ∈ Set.Icc (edgeVal K σ 1) E, (mExt K σ t).im = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h1' | h1'
      · rw [← h1']; exact hi1
      exact qc_im_zero_top K σ hσ hK hpos.le h1' fun u hu => (qc_supp_mem_Icc K σ hσ hK hS hu).2
    have := (qc_real_on K σ hσ hK hpos h1.le hre).2
    rw [hr1, qc_P_one K σ hσ hK hS] at this
    rw [hn, ← this]
    simp
  · -- in the gap `g`
    have hpos := qc_edge_pos h hK (k := 2 * g) (by omega) (by omega)
    obtain ⟨hi2, hr2⟩ := qc_edge_real K σ hσ hK hS (k := 2 * g) (by omega) (by omega)
      (qc_inner_fin (by omega))
    have h0 : 0 ≤ edgeVal K σ (2 * g + 1) :=
      (qc_edge_nonneg h hK (k := 2 * g + 1) (by omega) (by omega)).1
    have hre : ∀ t ∈ Set.Icc E (edgeVal K σ (2 * g)), (mExt K σ t).im = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2]; exact hi2
      exact qc_im_zero_gap K σ hσ hK h0 ⟨lt_of_lt_of_le hgl ht.1, h2⟩ (qc_supp_gap h hK hg1 hg)
    have hP := (qc_real_on K σ hσ hK hE hgr.le hre).2
    rw [hr2] at hP
    have hn : nClass K σ E = (K : ℝ) * (varrho K σ (Set.Ici (edgeVal K σ (2 * g)))).toReal := by
      unfold nClass
      congr 2
      have hgap : ∀ t ∈ Set.Ioo E (edgeVal K σ (2 * g)), t ∉ (varrho K σ).support := by
        intro t ht hs
        rcases qc_supp_gap h hK hg1 hg t hs with h' | h'
        · linarith [ht.1]
        · linarith [ht.2]
      have e1 := qc_Ici_split K σ (a := E) (b := E) le_rfl
      rw [Set.Icc_self, qc_varrho_singleton K σ hE, zero_add] at e1
      rw [e1, qc_Ioi_gap K σ hgr.le hpos hgap]
    rw [hn, qc_Ici_bands h hK g hg1 hg.le, qc_sum_P h hK g hg1 hg, hP]
  · -- below `a_{2p}`
    set p := numBands K σ
    have hy0 : yEdge K σ ≠ 0 := by
      intro hy
      have : edgeVal K σ (2 * p) = 0 := by
        unfold edgeVal
        simp [p, hy, FChart]
      linarith
    have hfin : ¬ (2 * p = 2 * p ∧ yEdge K σ = 0) := fun hc => hy0 hc.2
    obtain ⟨hi2, hr2⟩ := qc_edge_real K σ hσ hK hS (k := 2 * p) (by omega) le_rfl hfin
    have hre : ∀ t ∈ Set.Icc E (edgeVal K σ (2 * p)), (mExt K σ t).im = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2]; exact hi2
      exact qc_im_zero_gap K σ hσ hK le_rfl ⟨lt_of_lt_of_le hE ht.1, h2⟩ (qc_supp_bottom h hK)
    obtain ⟨hsg, hP⟩ := qc_real_on K σ hσ hK hE h3.le hre
    rw [hr2] at hsg hP
    have hx : xCrit K σ (2 * p) = (yEdge K σ)⁻¹ := by unfold xCrit; simp [p]
    have hxneg : xCrit K σ (2 * p) < 0 := by
      by_contra hc
      push Not at hc
      have hx0 : xCrit K σ (2 * p) ≠ 0 := by rw [hx]; exact inv_ne_zero hy0
      have := hsg.2 (lt_of_le_of_ne hc (Ne.symm hx0))
      linarith
    have hyneg : yEdge K σ < 0 := by
      rw [hx] at hxneg; exact inv_lt_zero.mp hxneg
    obtain ⟨hchart, hF⟩ := yEdge_spec K σ hσ hK hS
    -- every pole lies above `x_{2p}`
    have hall : qcP σ (xCrit K σ (2 * p)) = (Finset.univ.filter fun i => 0 < σ i).card := by
      unfold qcP
      congr 1
      refine Finset.filter_congr fun i _ => ?_
      rcases (hσ i).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · simp only [hpos, iff_true]
        have hc := hchart (σ i) (qc_mem_posVals hpos)
        rw [hx]
        have : 1 + σ i * (yEdge K σ)⁻¹ = (yEdge K σ + σ i) / yEdge K σ := by
          field_simp
        rw [this]
        exact div_neg_of_pos_of_neg hc hyneg
    -- `R ≤ 1`
    have hR : massRatio K σ ≤ 1 := by
      have := qc_FChart1_anti K σ hchart hyneg.le
      rw [qc_FChart1_zero, hF] at this
      linarith
    have hr : ((Finset.univ.filter fun i => 0 < σ i).card : ℝ) ≤ K := by
      unfold massRatio at hR
      rwa [div_le_one (by exact_mod_cast hK)] at hR
    -- `n(E) = K − K ϱ({0})`
    have hIio := qc_Iio_bottom h hK hE h3
    have hn : nClass K σ E = K - max ((K : ℝ) - (Finset.univ.filter fun i => 0 < σ i).card) 0 := by
      rw [← varrho_singleton_zero K σ hσ hK]
      unfold nClass
      rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, hIio,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
      ring
    rw [hn, hP, hall, max_eq_left (by linarith)]
    ring

/-- With a support point below `E`, `m(E + i0) < 0` off the support. -/
private lemma qc_neg_of_below {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {E : ℝ} (hE : 0 < E) (hns : E ∉ (varrho K σ).support)
    (hbelow : ∃ x ∈ (varrho K σ).support, x < E) : (mExt K σ E).re < 0 := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hp := card_innerCrit K σ hσ hK hS
  have him := qc_im_zero_of_not_mem K σ hσ hK hE.ne' hns
  obtain ⟨-, hx0, -, -⟩ := qc_real_facts K σ hσ hK hE.ne' him
  have key : ¬ 0 < (mExt K σ E).re → (mExt K σ E).re < 0 := fun hc =>
    lt_of_le_of_ne (not_lt.mp hc) hx0
  refine key fun hpos => ?_
  rcases qc_gap_cases h hK hE hns with h1 | ⟨g, hg1, hg, hgl, hgr⟩ | h3
  · have hpos1 := qc_edge_pos h hK (k := 1) le_rfl (by omega)
    obtain ⟨hi1, hr1⟩ := qc_edge_real K σ hσ hK hS (k := 1) le_rfl (by omega)
      (qc_inner_fin (by omega))
    have hre : ∀ t ∈ Set.Icc (edgeVal K σ 1) E, (mExt K σ t).im = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h1' | h1'
      · rw [← h1']; exact hi1
      exact qc_im_zero_top K σ hσ hK hpos1.le h1' fun u hu => (qc_supp_mem_Icc K σ hσ hK hS hu).2
    have := (qc_real_on K σ hσ hK hpos1 h1.le hre).1.2 hpos
    rw [hr1] at this
    have := (qc_mem_innerCrit K σ hσ hK (qc_xCrit_spec K σ hσ hK hS le_rfl (by omega)).1).1.1
    linarith
  · have hpos2 := qc_edge_pos h hK (k := 2 * g) (by omega) (by omega)
    obtain ⟨hi2, hr2⟩ := qc_edge_real K σ hσ hK hS (k := 2 * g) (by omega) (by omega)
      (qc_inner_fin (by omega))
    have h0 : 0 ≤ edgeVal K σ (2 * g + 1) :=
      (qc_edge_nonneg h hK (k := 2 * g + 1) (by omega) (by omega)).1
    have hre : ∀ t ∈ Set.Icc E (edgeVal K σ (2 * g)), (mExt K σ t).im = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2]; exact hi2
      exact qc_im_zero_gap K σ hσ hK h0 ⟨lt_of_lt_of_le hgl ht.1, h2⟩ (qc_supp_gap h hK hg1 hg)
    have := (qc_real_on K σ hσ hK hE hgr.le hre).1.1 hpos
    rw [hr2] at this
    have := (qc_mem_innerCrit K σ hσ hK
      (qc_xCrit_spec K σ hσ hK hS (k := 2 * g) (by omega) (by omega)).1).1.1
    linarith
  · set p := numBands K σ
    obtain ⟨x₀, hx₀, hx₀E⟩ := hbelow
    have hx₀0 : x₀ = 0 := by
      rcases qc_supp_bottom h hK x₀ hx₀ with h' | h'
      · exact le_antisymm h' (qc_supp_mem_Icc K σ hσ hK hS hx₀).1
      · linarith
    rw [hx₀0] at hx₀
    have hatom : 0 < varrho K σ {0} := by
      rw [← qc_Iio_bottom h hK hE h3]
      exact (Measure.mem_support_iff_forall _).1 hx₀ _ (Iio_mem_nhds hE)
    have hR : massRatio K σ < 1 := by
      by_contra hc
      push Not at hc
      have : varrho K σ {0} = 0 := by
        rw [varrho, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem rfl]
        rw [max_eq_right (by linarith), ENNReal.ofReal_zero, zero_smul, zero_add,
          withDensity_apply _ (measurableSet_singleton 0)]
        exact setLIntegral_measure_zero _ _ (by simp)
      rw [this] at hatom
      exact lt_irrefl _ hatom
    have hy0 : yEdge K σ ≠ 0 := by
      intro hy
      have : edgeVal K σ (2 * p) = 0 := by
        unfold edgeVal
        simp [p, hy, FChart]
      linarith
    have hfin : ¬ (2 * p = 2 * p ∧ yEdge K σ = 0) := fun hc => hy0 hc.2
    obtain ⟨hi2, hr2⟩ := qc_edge_real K σ hσ hK hS (k := 2 * p) (by omega) le_rfl hfin
    have hre : ∀ t ∈ Set.Icc E (edgeVal K σ (2 * p)), (mExt K σ t).im = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2]; exact hi2
      exact qc_im_zero_gap K σ hσ hK le_rfl ⟨lt_of_lt_of_le hE ht.1, h2⟩ (qc_supp_bottom h hK)
    have hxp := (qc_real_on K σ hσ hK hE h3.le hre).1.1 hpos
    rw [hr2] at hxp
    have hx : xCrit K σ (2 * p) = (yEdge K σ)⁻¹ := by unfold xCrit; simp [p]
    rw [hx] at hxp
    have hypos : 0 < yEdge K σ := inv_pos.mp hxp
    obtain ⟨-, hF⟩ := yEdge_spec K σ hσ hK hS
    have h0c : InChart σ 0 := fun s hs => by simpa using qc_pos_of_mem hs
    have := qc_FChart1_anti K σ h0c hypos.le
    rw [qc_FChart1_zero, hF] at this
    linarith

/-! ## `f_{N−1}` against `f_N` on the real line -/

private lemma qc_fR_mul (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) (x : ℝ) :
    (K : ℝ) * fR K σ x = -(K : ℝ) * x⁻¹ + ∑ i, σ i / (1 + σ i * x) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold fR
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 1 + σ i * x = 0
    · simp [h]
    · field_simp

private lemma qc_fR1_mul (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) (x : ℝ) :
    (K : ℝ) * fR1 K σ x = (K : ℝ) * (x ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (1 + σ i * x) ^ 2 := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold fR1
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : 1 + σ i * x = 0
  · simp [h]
  · field_simp

private lemma qc_fR2_mul (K : ℕ) (σ : Fin M → ℝ) (hK : 0 < K) (x : ℝ) :
    (K : ℝ) * fR2 K σ x = -2 * (K : ℝ) * (x ^ 3)⁻¹ + 2 * ∑ i, σ i ^ 3 / (1 + σ i * x) ^ 3 := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold fR2
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 1 + σ i * x = 0
    · simp [h]
    · field_simp

/-- `(N − 1) f_{N−1} = N f_N + x⁻¹`. -/
private lemma qc_fR_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (x : ℝ) :
    ((N : ℝ) - 1) * fR (N - 1) σ x = N * fR N σ x + x⁻¹ := by
  have h1 := qc_fR_mul (N - 1) σ (by omega) x
  have h2 := qc_fR_mul N σ (by omega) x
  rw [qc_cast_pred hN] at h1
  linear_combination h1 - h2

/-- `(N − 1) f'_{N−1} = N f'_N − x⁻²`. -/
private lemma qc_fR1_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (x : ℝ) :
    ((N : ℝ) - 1) * fR1 (N - 1) σ x = N * fR1 N σ x - (x ^ 2)⁻¹ := by
  have h1 := qc_fR1_mul (N - 1) σ (by omega) x
  have h2 := qc_fR1_mul N σ (by omega) x
  rw [qc_cast_pred hN] at h1
  linear_combination h1 - h2

/-- `(N − 1) f''_{N−1} = N f''_N + 2 x⁻³`. -/
private lemma qc_fR2_pred (σ : Fin M → ℝ) (hN : 2 ≤ N) (x : ℝ) :
    ((N : ℝ) - 1) * fR2 (N - 1) σ x = N * fR2 N σ x + 2 * (x ^ 3)⁻¹ := by
  have h1 := qc_fR2_mul (N - 1) σ (by omega) x
  have h2 := qc_fR2_mul N σ (by omega) x
  rw [qc_cast_pred hN] at h1
  linear_combination h1 - h2

/-- `C(τ/2)⁻¹ ≤ |m(E + i0)| ≤ C(τ/2)` for `τ ≤ E ≤ τ⁻¹`. -/
private lemma qc_mExt_norm_bounds {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    {E : ℝ} (h1 : τ ≤ E) (h2 : E ≤ τ⁻¹) :
    (genPropConst (τ / 2))⁻¹ ≤ ‖mExt K σ E‖ ∧ ‖mExt K σ E‖ ≤ genPropConst (τ / 2) := by
  have hτ := h.pos
  have hσ := h.nonneg
  have h2' := h.mono (show 0 < τ / 2 by positivity) (by linarith)
  have hE : E ≠ 0 := by linarith
  have ht := (continuous_norm.tendsto _).comp (qc_tendsto_mFun_path K σ hσ hE)
  have hev : ∀ᶠ y : ℝ in 𝓝[>] 0, (genPropConst (τ / 2))⁻¹ ≤
      ‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ∧
        ‖mFun K σ ((E : ℂ) + (y : ℂ) * Complex.I)‖ ≤ genPropConst (τ / 2) := by
    have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
    filter_upwards [Ioo_mem_nhdsGT hτi] with y hy
    have hy' : 0 < ((E : ℂ) + (y : ℂ) * Complex.I).im := by rw [qc_path_im]; exact hy.1
    have hn1 : τ / 2 ≤ ‖(E : ℂ) + (y : ℂ) * Complex.I‖ := by
      have := Complex.abs_re_le_norm ((E : ℂ) + (y : ℂ) * Complex.I)
      rw [qc_path_re, abs_of_pos (by linarith)] at this
      linarith
    have hn2 : ‖(E : ℂ) + (y : ℂ) * Complex.I‖ ≤ (τ / 2)⁻¹ := by
      have e : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
      rw [e]
      calc ‖(E : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(E : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |E| + |y| := by simp
        _ ≤ 2 * τ⁻¹ := by
            rw [abs_of_pos (by linarith), abs_of_pos hy.1]; linarith [hy.2]
    obtain ⟨a, b, -⟩ := gen_prop_m h2' hy' hn1 hn2
    exact ⟨a, b⟩
  exact ⟨ge_of_tendsto ht (hev.mono fun y hy => hy.1), le_of_tendsto ht (hev.mono fun y hy => hy.2)⟩

/-- For `a < b` with `[a, b)` off the support, `n(a) = n(b)`. -/
private lemma qc_nClass_eq_of_gap (K : ℕ) (σ : Fin M → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ t ∈ Set.Ico a b, t ∉ (varrho K σ).support) : nClass K σ a = nClass K σ b := by
  unfold nClass
  congr 2
  have h0 := qc_measure_null_of_subset K σ hgap
  rw [← Set.Ico_union_Ici_eq_Ici hab, measure_union _ measurableSet_Ici, h0, zero_add]
  rw [Set.disjoint_left]
  intro z hz1 hz2
  exact absurd hz1.2 (not_lt.mpr hz2)

/-! ## The count `n_{N−1}` against `n_N` in a gap -/

private lemma qc_nClass_zero_above {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ K σ)
    (hK : 0 < K) {E : ℝ} (hE : 2 * τ⁻¹ * (1 + τ⁻¹) < E) : nClass K σ E = 0 := by
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hp := card_innerCrit K σ hσ hK hS
  have ha1 := (qc_edge_nonneg h hK (k := 1) le_rfl (by omega)).2
  unfold nClass
  rw [qc_measure_null_of_subset K σ (S := Set.Ici E) fun t ht hs => by
    have := (qc_supp_mem_Icc K σ hσ hK hS hs).2
    linarith [Set.mem_Ici.mp ht]]
  simp

/-- In a gap of `ϱ` above `τ/2`, at distance `≥ τ/4` from `supp ϱ` and with a point of `supp ϱ`
below it: `n_{N−1}(E) = n_N(E)`. (Below the whole support, when rank `Σ ≥ N`, the two counts are
`N − 1` and `N`.) -/
theorem nClass_pred_gap (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ E : ℝ, τ / 2 ≤ E → τ / 4 ≤ Metric.infDist E (varrho N σ).support →
        (∃ x ∈ (varrho N σ).support, x < E) →
        nClass (N - 1) σ E = nClass N σ E := by
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  set Emax := 4 * τ⁻¹ * (1 + 2 * τ⁻¹) with hEmax
  have hEmax0 : 0 < Emax := by positivity
  set τ₁ := min (τ / 4) (Emax + 1)⁻¹ with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min (by positivity) (by positivity)
  set c := (genPropConst (τ₁ / 2))⁻¹ with hc
  have hc0 : 0 < c := by rw [hc, genPropConst]; positivity
  set d := τ / 8 with hd
  have hd0 : 0 < d := by positivity
  set B := Emax + 1 + c⁻¹ with hB
  have hB0 : 0 < B := by positivity
  refine ⟨⌈(d ^ 2 * c ^ 2)⁻¹ + 4 * B / d + 3⌉₊, ?_⟩
  intro N hN M σ h E hE hdist hbelow
  have hNc : (d ^ 2 * c ^ 2)⁻¹ + 4 * B / d + 3 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNr : (3 : ℝ) ≤ N := by
    have : 0 ≤ (d ^ 2 * c ^ 2)⁻¹ + 4 * B / d := by positivity
    linarith
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hσ := h.nonneg
  have h1 := qc_da_pred h hN2
  have hcast := qc_cast_pred hN2
  have hτ1 : τ ≤ 1 := by
    have h' : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
    linarith
  have hd1 : d ≤ 1 := by rw [hd]; linarith
  -- above the supports both counts vanish
  have hbd1 : 2 * τ⁻¹ * (1 + τ⁻¹) ≤ Emax := by rw [hEmax]; nlinarith
  have hbd2 : 2 * (τ / 2)⁻¹ * (1 + (τ / 2)⁻¹) = Emax := by rw [hEmax]; field_simp; ring
  by_cases hbig : Emax < E
  · rw [qc_nClass_zero_above h hK (by linarith), qc_nClass_zero_above h1 hK1 (by linarith)]
  push Not at hbig
  -- the points `E' ∈ [E − τ/8, E + τ/8]`
  have hnot : E ∉ (varrho N σ).support := fun hs => by
    have := Metric.infDist_zero_of_mem hs
    linarith
  have hdist' : ∀ E' ∈ Set.Icc (E - d) (E + d), ∀ u ∈ (varrho N σ).support, d ≤ |u - E'| := by
    intro E' hE' u hu
    have h1' := Metric.infDist_le_dist_of_mem hu (x := E)
    rw [Real.dist_eq] at h1'
    have : |E - u| ≤ |u - E'| + |E' - E| := by
      calc |E - u| = |(E' - u) + (E - E')| := by ring_nf
        _ ≤ |E' - u| + |E - E'| := abs_add_le _ _
        _ = |u - E'| + |E' - E| := by rw [abs_sub_comm E' u, abs_sub_comm E E']
    have : |E' - E| ≤ d := abs_le.2 ⟨by linarith [hE'.1], by linarith [hE'.2]⟩
    linarith
  set X : ℝ → ℝ := fun E' => (mExt N σ E').re with hX
  set T : ℝ → ℝ := fun E' => fR (N - 1) σ (X E') with hT
  have hfacts : ∀ E' ∈ Set.Icc (E - d) (E + d),
      0 < E' ∧ mExt N σ E' = (X E' : ℂ) ∧ X E' ≠ 0 ∧ (∀ i, 1 + σ i * X E' ≠ 0) ∧
        fR N σ (X E') = E' ∧ c ≤ |X E'| ∧ 0 < fR1 (N - 1) σ (X E') ∧
        |T E' - E'| ≤ d / 4 := by
    intro E' hE'
    have hE'0 : 0 < E' := by linarith [hE'.1]
    have him := qc_mExt_im_eq_zero N σ hσ hK hE'0.ne' hd0 (hdist' E' hE')
    obtain ⟨hwx, hx0, hpole, hf⟩ := qc_real_facts N σ hσ hK hE'0.ne' him
    have hge := qc_fR1_ge_dist N σ hσ hK hE'0.ne' hd0 (hdist' E' hE')
    have hlo : c ≤ |X E'| := by
      have hτ₁E : τ₁ ≤ E' := (min_le_left _ _).trans (by linarith [hE'.1])
      have hEτ₁ : E' ≤ τ₁⁻¹ := by
        have : E' ≤ Emax + 1 := by linarith [hE'.2]
        refine this.trans ?_
        rw [hτ₁]
        exact le_inv_of_le_inv₀ (by positivity) (min_le_right _ _)
      have := (qc_mExt_norm_bounds (h.mono hτ₁0 ((min_le_left _ _).trans (by linarith)))
        hτ₁E hEτ₁).1
      rw [hwx, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have hx2 : (X E' ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have := pow_le_pow_left₀ hc0.le hlo 2
      rwa [sq_abs] at this
    have hd' : 0 < fR1 (N - 1) σ (X E') := by
      have e := qc_fR1_pred σ hN2 (X E')
      have hN1 : (0 : ℝ) < N - 1 := by linarith
      have : (c ^ 2)⁻¹ < N * d ^ 2 := by
        have h3 : (d ^ 2 * c ^ 2)⁻¹ < N := by
          have : 0 ≤ 4 * B / d := by positivity
          linarith
        rw [inv_lt_iff_one_lt_mul₀ (by positivity)] at h3
        rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
        nlinarith
      have : 0 < ((N : ℝ) - 1) * fR1 (N - 1) σ (X E') := by
        rw [e]; nlinarith
      exact pos_of_mul_pos_right this hN1.le
    have hTE : |T E' - E'| ≤ d / 4 := by
      have e := qc_fR_pred σ hN2 (X E')
      have hN1 : (0 : ℝ) < N - 1 := by linarith
      have e2 : T E' - E' = (E' + (X E')⁻¹) / (N - 1) := by
        simp only [hT]
        rw [eq_div_iff hN1.ne', sub_mul, mul_comm, e, hf]
        ring
      rw [e2, abs_div, abs_of_pos hN1, div_le_iff₀ hN1]
      have hinv : |(X E')⁻¹| ≤ c⁻¹ := by
        rw [abs_inv]; exact inv_anti₀ hc0 hlo
      have h5 : |E' + (X E')⁻¹| ≤ B := by
        calc |E' + (X E')⁻¹| ≤ |E'| + |(X E')⁻¹| := abs_add_le _ _
          _ ≤ (Emax + 1) + c⁻¹ := by
              rw [abs_of_pos hE'0]; linarith [hE'.2]
          _ = B := rfl
      have h6 : 4 * B / d ≤ N - 1 := by
        have : 0 ≤ (d ^ 2 * c ^ 2)⁻¹ := by positivity
        linarith
      rw [div_le_iff₀ hd0] at h6
      linarith
    exact ⟨hE'0, hwx, hx0, hpole, hf, hlo, hd', hTE⟩
  -- `T` is continuous on the interval and maps it off the support at `N − 1`
  have hcont : ContinuousOn T (Set.Icc (E - d) (E + d)) := by
    have hXc : ContinuousOn X (Set.Icc (E - d) (E + d)) :=
      Complex.continuous_re.comp_continuousOn (qc_cont_mExt N σ hσ (by linarith))
    intro E' hE'
    obtain ⟨-, -, hx0, hpole, -⟩ := hfacts E' hE'
    exact (hasDerivAt_fR (N - 1) σ hx0 hpole).continuousAt.comp_continuousWithinAt (hXc E' hE')
  have hoff : ∀ t ∈ Set.Icc (T (E - d)) (T (E + d)), t ∉ (varrho (N - 1) σ).support := by
    intro t ht
    obtain ⟨E', hE', hTt⟩ := intermediate_value_Icc (show E - d ≤ E + d by linarith) hcont ht
    obtain ⟨-, -, hx0, hpole, -, -, hd', hTE⟩ := hfacts E' hE'
    have hT0 : 0 < T E' := by
      have := (abs_le.1 hTE).1
      linarith [hE'.1]
    rw [← hTt]
    exact qc_not_mem_support (N - 1) σ hσ hK1 hx0 hpole hd' hT0
  have hm := hfacts (E - d) ⟨le_rfl, by linarith⟩
  have hp := hfacts (E + d) ⟨by linarith, le_rfl⟩
  have h0 := hfacts E ⟨by linarith, by linarith⟩
  obtain ⟨hE0, hwx, hx0, hpole, hf, -, hd', hTE⟩ := h0
  have hTm := (abs_le.1 hm.2.2.2.2.2.2.2).2
  have hTp := (abs_le.1 hp.2.2.2.2.2.2.2).1
  have hTE' := abs_le.1 hTE
  have hT0 : 0 < T E := by linarith
  -- `n_{N−1}(E) = n_{N−1}(T E)`
  have hseg : nClass (N - 1) σ E = nClass (N - 1) σ (T E) := by
    rcases le_total E (T E) with hle | hle
    · exact qc_nClass_eq_of_gap (N - 1) σ hle fun t ht =>
        hoff t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact (qc_nClass_eq_of_gap (N - 1) σ hle fun t ht =>
        hoff t ⟨by linarith [ht.1], by linarith [ht.2]⟩).symm
  -- the two counts
  have hneg := qc_neg_of_below h hK hE0 hnot hbelow
  have hcN := qc_count h hK hE0 hnot hneg
  have hmT : mExt (N - 1) σ (T E) = X E := by
    have := mExt_fR_of_pos (N - 1) σ hσ hK1 hx0 hpole hT0.ne' hd'
    exact this
  have hnotT : T E ∉ (varrho (N - 1) σ).support := hoff _ ⟨by linarith, by linarith⟩
  have hc1 := qc_count h1 hK1 hT0 hnotT (by rw [hmT]; simpa [hX] using hneg)
  rw [hseg, hc1, hcN, hmT]
  simp [hX]

/-! ## The chart of `I_0` and the critical points -/

private lemma qc_sum_group (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (g : ℝ → ℝ) (hg : g 0 = 0) :
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

/-- `f'(1/y) = −y² F'(y)` in the chart of `I_0`. -/
private lemma qc_fR1_inv (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy0 : y ≠ 0)
    (hy : InChart σ y) : fR1 K σ y⁻¹ = -(y ^ 2) * FChart1 K σ y := by
  have hg : ∑ i, σ i ^ 2 / ((K : ℝ) * (1 + σ i * y⁻¹) ^ 2) =
      ∑ s ∈ posVals σ, ((Finset.univ.filter fun i => σ i = s).card : ℝ) *
        (s ^ 2 / ((K : ℝ) * (1 + s * y⁻¹) ^ 2)) :=
    qc_sum_group σ hσ (fun a => a ^ 2 / ((K : ℝ) * (1 + a * y⁻¹) ^ 2)) (by simp)
  have hterm : ∀ s ∈ posVals σ, ((Finset.univ.filter fun i => σ i = s).card : ℝ) *
      (s ^ 2 / ((K : ℝ) * (1 + s * y⁻¹) ^ 2)) =
      y ^ 2 * (weight K σ s * s ^ 2 / (y + s) ^ 2) := by
    intro s hs
    have h1 := (hy s hs).ne'
    have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
    rw [e, weight]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · have hKr : (K : ℝ) ≠ 0 := by positivity
      field_simp
  unfold fR1 FChart1
  rw [hg, Finset.sum_congr rfl hterm, ← Finset.mul_sum, inv_pow, inv_inv]
  ring

private lemma qc_inv_nonpole {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy0 : y ≠ 0)
    (hy : InChart σ y) : ∀ i, 1 + σ i * y⁻¹ ≠ 0 := by
  intro i
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have h1 := hy (σ i) (qc_mem_posVals hpos)
    have e : 1 + σ i * y⁻¹ = (y + σ i) / y := by field_simp
    rw [e]
    exact div_ne_zero h1.ne' hy0

/-- `x_{2p} = 1/y_{2p}` is not in the inner region. -/
private lemma qc_inv_not_inner {σ : Fin M → ℝ} {y : ℝ} (hy0 : y ≠ 0) (hy : InChart σ y) :
    ¬ InInner σ y⁻¹ := by
  rintro ⟨hneg, s, hs, hpos⟩
  have hyneg : y < 0 := inv_lt_zero.mp hneg
  have e : 1 + s * y⁻¹ = (y + s) / y := by field_simp
  rw [e] at hpos
  have := div_neg_of_pos_of_neg (hy s hs) hyneg
  linarith

/-- Every finite `x_k` is a critical point: `f'(x_k) = 0`, `x_k ≠ 0`, not a pole. -/
private lemma qc_xCrit_crit (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * numBands K σ)
    (hfin : ¬ (k = 2 * numBands K σ ∧ yEdge K σ = 0)) :
    xCrit K σ k ≠ 0 ∧ (∀ i, 1 + σ i * xCrit K σ k ≠ 0) ∧ fR1 K σ (xCrit K σ k) = 0 := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · obtain ⟨hin, hnp, h1⟩ := qc_mem_innerCrit K σ hσ hK (qc_xCrit_spec K σ hσ hK hS hk1 hlt).1
    exact ⟨hin.1.ne, hnp, h1⟩
  · have hy0 : yEdge K σ ≠ 0 := fun h => hfin ⟨heq, h⟩
    obtain ⟨hch, hF⟩ := yEdge_spec K σ hσ hK hS
    have hx : xCrit K σ k = (yEdge K σ)⁻¹ := by
      unfold xCrit; rw [ite_eq_left_iff.mpr (fun h => absurd heq h)]
    rw [hx]
    refine ⟨inv_ne_zero hy0, qc_inv_nonpole hσ hy0 hch, ?_⟩
    rw [qc_fR1_inv K σ hσ hy0 hch, hF, mul_zero]

/-! ## Each edge at `N − 1` lies near an edge at `N` -/

/-- An edge `ȧ_i ≥ τ'` of `N − 1` has a point `g` off `supp ϱ_N` within `B/N`, with
`m_N(g + i0) = ẋ_i`, and an edge `a_e` of `N` within `D` of `g`. -/
private lemma qc_edge_near (τ τ' D : ℝ) (hτ : 0 < τ) (hτ' : 0 < τ') (hD : 0 < D)
    (hDτ : D ≤ τ' / 2) :
    ∃ B : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ i, 1 ≤ i → i ≤ 2 * numBands (N - 1) σ → τ' ≤ edgeVal (N - 1) σ i →
        ∃ g, 0 < g ∧ g ∉ (varrho N σ).support ∧ mExt N σ g = xCrit (N - 1) σ i ∧
          |g - edgeVal (N - 1) σ i| ≤ B / N ∧
          ∃ e, 1 ≤ e ∧ e ≤ 2 * numBands N σ ∧ |edgeVal N σ e - g| < D := by
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  set Emax := 4 * τ⁻¹ * (1 + 2 * τ⁻¹) with hEmax
  have hEmax0 : 0 < Emax := by positivity
  set τ₁ := min τ' Emax⁻¹ with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min hτ' (by positivity)
  set c := (genPropConst (τ₁ / 2))⁻¹ with hc
  have hc0 : 0 < c := by rw [hc, genPropConst]; positivity
  set B := Emax + c⁻¹ with hB
  have hB0 : 0 < B := by positivity
  refine ⟨B, ⌈2 * B / τ' + (c ^ 2 * D ^ 2)⁻¹ + 2⌉₊, ?_⟩
  intro N hN M σ h i hi1 hi hτ'i
  have hNc : 2 * B / τ' + (c ^ 2 * D ^ 2)⁻¹ + 2 ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by
      have : 0 ≤ 2 * B / τ' + (c ^ 2 * D ^ 2)⁻¹ := by positivity
      linarith
    exact_mod_cast this
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have h1 := qc_da_pred h hN2
  have hbd2 : 2 * (τ / 2)⁻¹ * (1 + (τ / 2)⁻¹) = Emax := by rw [hEmax]; field_simp; ring
  have hup : edgeVal (N - 1) σ i ≤ Emax := hbd2 ▸ (qc_edge_nonneg h1 hK1 hi1 hi).2
  have hpos : 0 < edgeVal (N - 1) σ i := lt_of_lt_of_le hτ' hτ'i
  -- the boundary value at the edge of `N − 1`
  have hfin : ¬ (i = 2 * numBands (N - 1) σ ∧ yEdge (N - 1) σ = 0) := by
    rintro ⟨hi', hy⟩
    have : edgeVal (N - 1) σ i = 0 := by
      unfold edgeVal; simp [hi', hy, FChart]
    linarith
  obtain ⟨hx0, hnp, hcrit⟩ := qc_xCrit_crit (N - 1) σ hσ hK1 hS hi1 hi hfin
  have hm := mExt_edgeVal (N - 1) σ hσ hK1 hS hi1 hi hfin
  set x := xCrit (N - 1) σ i with hxdef
  have hlo : c ≤ |x| := by
    have hτ₁E : τ₁ ≤ edgeVal (N - 1) σ i := (min_le_left _ _).trans hτ'i
    have hEτ₁ : edgeVal (N - 1) σ i ≤ τ₁⁻¹ :=
      hup.trans (le_inv_of_le_inv₀ (by positivity) (min_le_right _ _))
    have hτ₁τ : τ₁ ≤ τ / 2 := by
      have : τ₁ ≤ Emax⁻¹ := min_le_right _ _
      refine this.trans ?_
      rw [inv_le_comm₀ hEmax0 (by positivity), hEmax]
      have : (τ / 2)⁻¹ = 2 * τ⁻¹ := by field_simp
      rw [this]
      nlinarith
    have := (qc_mExt_norm_bounds (h1.mono hτ₁0 hτ₁τ) hτ₁E hEτ₁).1
    rw [hm, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  -- `f'_N(x) = 1/(N x²)`
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hd1 : fR1 N σ x = (N : ℝ)⁻¹ * (x ^ 2)⁻¹ := by
    have e := qc_fR1_pred σ hN2 x
    rw [hcrit, mul_zero] at e
    have h3 : (N : ℝ) * fR1 N σ x = (x ^ 2)⁻¹ := by linarith
    rw [← h3, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hd1pos : 0 < fR1 N σ x := by rw [hd1]; positivity
  set g := fR N σ x with hg
  have hfa : fR (N - 1) σ x = edgeVal (N - 1) σ i :=
    (edgeVal_eq_fR (N - 1) σ hσ hK1 hS hi1 hi hfin).symm
  have hgE : |g - edgeVal (N - 1) σ i| ≤ B / N := by
    have e := qc_fR_pred σ hN2 x
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have e2 : g - fR (N - 1) σ x = -(fR (N - 1) σ x + x⁻¹) / N := by
      rw [eq_div_iff hN0]
      linear_combination -e
    rw [← hfa, e2, abs_div, abs_neg, Nat.abs_cast, div_le_div_iff_of_pos_right (by positivity)]
    have hinv : |x⁻¹| ≤ c⁻¹ := by rw [abs_inv]; exact inv_anti₀ hc0 hlo
    calc |fR (N - 1) σ x + x⁻¹| ≤ |fR (N - 1) σ x| + |x⁻¹| := abs_add_le _ _
      _ ≤ Emax + c⁻¹ := by
          rw [hfa, abs_of_pos hpos]
          linarith
  have hBN : B / N ≤ τ' / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * B / τ' ≤ N := by
      have : 0 ≤ (c ^ 2 * D ^ 2)⁻¹ := by positivity
      linarith
    rw [div_le_iff₀ hτ'] at this
    linarith
  have hgpos : τ' / 2 ≤ g := by
    have := (abs_le.1 hgE).1
    linarith
  have hg0 : 0 < g := by linarith
  have hmg : mExt N σ g = x := mExt_fR_of_pos N σ hσ hK hx0 hnp hg0.ne' hd1pos
  have hns : g ∉ (varrho N σ).support := qc_not_mem_support N σ hσ hK hx0 hnp hd1pos hg0
  refine ⟨g, hg0, hns, hmg, hgE, ?_⟩
  -- a support point within `D`
  have hex : ∃ u ∈ (varrho N σ).support, |u - g| < D := by
    by_contra hno
    push Not at hno
    have hge := qc_fR1_ge_dist N σ hσ hK hg0.ne' hD hno
    rw [hmg, Complex.ofReal_re, hd1] at hge
    have hx2 : (x ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have := pow_le_pow_left₀ hc0.le hlo 2
      rwa [sq_abs] at this
    have h3 : (c ^ 2 * D ^ 2)⁻¹ < N := by
      have : 0 ≤ 2 * B / τ' := by positivity
      linarith
    have h4 : (N : ℝ)⁻¹ * (x ^ 2)⁻¹ < D ^ 2 := by
      calc (N : ℝ)⁻¹ * (x ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ * (c ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hx2 (by positivity)
        _ < D ^ 2 := by
            rw [← mul_inv, inv_lt_comm₀ (by positivity) (by positivity)]
            rw [inv_lt_comm₀ (by positivity) (by positivity)] at h3
            calc (D ^ 2)⁻¹ = c ^ 2 * (c ^ 2 * D ^ 2)⁻¹ := by field_simp
              _ < c ^ 2 * N := mul_lt_mul_of_pos_left (by
                  rw [inv_lt_comm₀ (by positivity) (by positivity)]; exact h3) (by positivity)
              _ = _ := by ring
    linarith
  obtain ⟨u, hu, hug⟩ := hex
  have hu0 : 0 < u := by
    have := (abs_lt.1 hug).1
    linarith
  obtain ⟨b, hb1, hb, hbl, hbr⟩ := qc_supp_band N σ hσ hK hS hu0 hu
  have hgb : ¬ (edgeVal N σ (2 * b) ≤ g ∧ g ≤ edgeVal N σ (2 * b - 1)) := fun hm' =>
    hns ((mem_support_varrho_iff N σ hσ hK hS hg0).2 ⟨b, hb1, hb, hm'⟩)
  by_cases hgl : g < edgeVal N σ (2 * b)
  · refine ⟨2 * b, by omega, by omega, ?_⟩
    rw [abs_lt] at hug ⊢
    constructor <;> linarith
  · push Not at hgl
    have hgr : edgeVal N σ (2 * b - 1) < g := by
      by_contra hc'
      exact hgb ⟨hgl, not_lt.mp hc'⟩
    refine ⟨2 * b - 1, by omega, by omega, ?_⟩
    rw [abs_lt] at hug ⊢
    constructor <;> linarith

/-! ## The window around a regular critical point `x_k` -/

private lemma qc_edge_consts {τ : ℝ} (hτ : 0 < τ) :
    0 < edgecx τ ∧ 0 < edgec2 τ ∧ 0 < edgeC3 τ ∧ 0 < edgeRho1 τ ∧
      edgeRho1 τ ≤ edgeRho0 τ ∧ edgeRho0 τ ≤ edgecx τ / 2 ∧ edgeRho0 τ ≤ τ / 2 ∧
      edgeC3 τ * edgeRho1 τ ≤ edgec2 τ / 4 := by
  have hs := Real.sqrt_pos.2 hτ
  have h1 : 0 < edgecx τ := by unfold edgecx; positivity
  have h2 : 0 < edgeCx τ := by unfold edgeCx; positivity
  have h4 : 0 < edgec2 τ := by unfold edgec2; positivity
  have h5 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h7 : 0 < edgeRho1 τ := by unfold edgeRho1 edgeRho0; positivity
  refine ⟨h1, h4, h5, h7, min_le_left _ _, ?_, ?_, ?_⟩
  · unfold edgeRho0; linarith [min_le_left (edgecx τ) τ]
  · unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  · have := min_le_right (edgeRho0 τ) (edgec2 τ / (4 * edgeC3 τ))
    calc edgeC3 τ * edgeRho1 τ ≤ edgeC3 τ * (edgec2 τ / (4 * edgeC3 τ)) :=
          mul_le_mul_of_nonneg_left this h5.le
      _ = edgec2 τ / 4 := by field_simp

private lemma qc_sign_sq (k : ℕ) : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
  rw [← pow_mul]; exact (Even.neg_one_pow ⟨k + 1, by ring⟩)

private lemma qc_sign_abs (k : ℕ) : |(-1 : ℝ) ^ (k + 1)| = 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- The real window `x_k + ε t`, `|t| ≤ ρ₁`, `ε = (−1)^{k+1}`, around a regular critical point. -/
private lemma qc_win_N {τ : ℝ} {K : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ K σ)
    (hk : RegularEdge τ K σ k) {t : ℝ} (ht : |t| ≤ edgeRho1 τ) :
    let x := xCrit K σ k
    let ε := (-1 : ℝ) ^ (k + 1)
    (x + ε * t ≠ 0 ∧ (∀ i, 1 + σ i * (x + ε * t) ≠ 0) ∧ edgecx τ / 2 ≤ |x + ε * t|) ∧
    3 * edgec2 τ / 4 ≤ ε * fR2 K σ (x + ε * t) ∧
    (0 ≤ t → 3 * edgec2 τ / 4 * t ≤ fR1 K σ (x + ε * t)) ∧
    (t ≤ 0 → fR1 K σ (x + ε * t) ≤ 3 * edgec2 τ / 4 * t) ∧
    edgec2 τ / 4 * t ^ 2 ≤ ε * (fR K σ (x + ε * t) - edgeVal K σ k) ∧
    |fR K σ (x + ε * t) - edgeVal K σ k| ≤ (edgeC2 τ / 2 + edgec2 τ / 4) * t ^ 2 := by
  intro x ε
  have hτ := h.pos
  obtain ⟨hcx, hc2, hC3, hρ, hρ10, hρ0c, hρ0τ, hC3ρ⟩ := qc_edge_consts hτ
  obtain ⟨hxl, -, -⟩ := xCrit_bounds h hk
  have hc2x := edgec2_le_fR2_xCrit h hk
  have hC2x := abs_fR2_xCrit_le h hk
  have hε2 : ε * ε = 1 := by rw [← sq]; exact qc_sign_sq k
  have hεa : |ε| = 1 := qc_sign_abs k
  set y := x + ε * t with hy
  have hyx : ‖((y : ℝ) : ℂ) - (x : ℂ)‖ = |t| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hy, add_sub_cancel_left,
      abs_mul, hεa, one_mul]
  have hζ : ‖((y : ℝ) : ℂ) - (xCrit K σ k : ℂ)‖ ≤ edgeRho0 τ := by
    rw [hyx]; exact ht.trans hρ10
  obtain ⟨hy0, hynp, -⟩ := norm_fCDeriv3_le h hk hζ
  obtain ⟨hT2, hT1, hT0⟩ := edge_taylor h hk hζ
  rw [fCDeriv2_ofReal, fCDeriv_ofReal, fC_ofReal, hyx] at *
  have hT2' : |fR2 K σ y - fR2 K σ x| ≤ edgeC3 τ * |t| := by
    rw [← Complex.ofReal_sub, Complex.norm_real] at hT2; exact hT2
  have hT1' : |fR1 K σ y - fR2 K σ x * (ε * t)| ≤ edgeC3 τ * |t| ^ 2 := by
    have e : (fR1 K σ y : ℂ) - (fR2 K σ x : ℂ) * ((y : ℂ) - (x : ℂ)) =
        ((fR1 K σ y - fR2 K σ x * (ε * t) : ℝ) : ℂ) := by
      rw [hy]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hT1; exact hT1
  have hT0' : |fR K σ y - edgeVal K σ k - fR2 K σ x / 2 * t ^ 2| ≤ edgeC3 τ * |t| ^ 3 := by
    have e : (fR K σ y : ℂ) - (edgeVal K σ k : ℂ) - (fR2 K σ x : ℂ) / 2 * ((y : ℂ) - (x : ℂ)) ^ 2 =
        ((fR K σ y - edgeVal K σ k - fR2 K σ x / 2 * t ^ 2 : ℝ) : ℂ) := by
      rw [hy]; push_cast
      have : ((ε : ℝ) : ℂ) ^ 2 = 1 := by
        rw [← Complex.ofReal_pow, qc_sign_sq k]; simp
      linear_combination (-(fR2 K σ x : ℂ) / 2 * (t : ℂ) ^ 2) * this
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hT0; exact hT0
  have hnp' : ∀ i, 1 + σ i * y ≠ 0 := by
    intro i hi
    apply hynp i
    rw [← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_add, hi]; simp
  have hy0' : y ≠ 0 := by
    intro h0; apply hy0; rw [h0]; simp
  have hC3t : edgeC3 τ * |t| ≤ edgec2 τ / 4 :=
    (mul_le_mul_of_nonneg_left ht hC3.le).trans hC3ρ
  have hta : 0 ≤ |t| := abs_nonneg t
  refine ⟨⟨hy0', hnp', ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : |x| ≤ |y| + |ε * t| := by
      calc |x| = |y - ε * t| := by rw [hy]; ring_nf
        _ ≤ |y| + |ε * t| := abs_sub _ _
    rw [abs_mul, hεa, one_mul] at h1
    linarith
  · have e : ε * fR2 K σ y = ε * fR2 K σ x + ε * (fR2 K σ y - fR2 K σ x) := by ring
    have h2 : |ε * (fR2 K σ y - fR2 K σ x)| ≤ edgec2 τ / 4 := by
      rw [abs_mul, hεa, one_mul]; linarith
    rw [e]
    have := (abs_le.1 h2).1
    linarith
  · intro ht0
    have e : fR2 K σ x * (ε * t) = (ε * fR2 K σ x) * t := by ring
    rw [e] at hT1'
    have h3 := (abs_le.1 hT1').1
    have h4 : edgec2 τ * t ≤ (ε * fR2 K σ x) * t := mul_le_mul_of_nonneg_right hc2x ht0
    have h5 : edgeC3 τ * |t| ^ 2 ≤ edgec2 τ / 4 * t := by
      rw [abs_of_nonneg ht0] at hC3t ⊢
      nlinarith
    linarith
  · intro ht0
    have e : fR2 K σ x * (ε * t) = (ε * fR2 K σ x) * t := by ring
    rw [e] at hT1'
    have h3 := (abs_le.1 hT1').2
    have h4 : (ε * fR2 K σ x) * t ≤ edgec2 τ * t := mul_le_mul_of_nonpos_right hc2x ht0
    have h5 : edgeC3 τ * |t| ^ 2 ≤ -(edgec2 τ / 4 * t) := by
      rw [abs_of_nonpos ht0] at hC3t ⊢
      nlinarith
    linarith
  · have h3 := (abs_le.1 hT0').1
    have h3' : -(edgeC3 τ * |t| ^ 3) ≤ ε * (fR K σ y - edgeVal K σ k - fR2 K σ x / 2 * t ^ 2) := by
      have := abs_le.1 hT0'
      rcases le_or_gt 0 ε with hεp | hεn
      · have hε1 : ε = 1 := by
          have := hεa; rw [abs_of_nonneg hεp] at this; exact this
        rw [hε1]; linarith
      · have hε1 : ε = -1 := by
          have := hεa; rw [abs_of_neg hεn] at this; linarith
        rw [hε1]; linarith
    have e : ε * (fR K σ y - edgeVal K σ k - fR2 K σ x / 2 * t ^ 2) =
        ε * (fR K σ y - edgeVal K σ k) - (ε * fR2 K σ x) / 2 * t ^ 2 := by ring
    rw [e] at h3'
    have h4 : edgec2 τ / 2 * t ^ 2 ≤ (ε * fR2 K σ x) / 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
    have h5 : edgeC3 τ * |t| ^ 3 ≤ edgec2 τ / 4 * t ^ 2 := by
      have : |t| ^ 3 = |t| * t ^ 2 := by rw [pow_succ, sq_abs]; ring
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hC3t (sq_nonneg t)
    linarith
  · have h5 : edgeC3 τ * |t| ^ 3 ≤ edgec2 τ / 4 * t ^ 2 := by
      have : |t| ^ 3 = |t| * t ^ 2 := by rw [pow_succ, sq_abs]; ring
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hC3t (sq_nonneg t)
    have h6 : |fR2 K σ x / 2 * t ^ 2| ≤ edgeC2 τ / 2 * t ^ 2 := by
      rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg t)]
      have : |(2 : ℝ)| = 2 := abs_two
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
    calc |fR K σ y - edgeVal K σ k|
        = |(fR K σ y - edgeVal K σ k - fR2 K σ x / 2 * t ^ 2) + fR2 K σ x / 2 * t ^ 2| := by
          ring_nf
      _ ≤ |fR K σ y - edgeVal K σ k - fR2 K σ x / 2 * t ^ 2| + |fR2 K σ x / 2 * t ^ 2| :=
          abs_add_le _ _
      _ ≤ _ := by nlinarith

/-! ## Indices of critical points -/

/-- A point of `𝒞 ∩ (I_1 ∪ ⋯ ∪ I_n)` is `x_l` for some `l < 2p`. -/
private lemma qc_exists_index (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {x : ℝ} (hx : x ∈ innerCrit K σ) :
    ∃ l, 1 ≤ l ∧ l < 2 * numBands K σ ∧ xCrit K σ l = x := by
  have hc := (card_innerCrit K σ hσ hK hS).1
  set L := ((innerCrit K σ).sort (· ≤ ·)).reverse with hL
  have hlen : L.length = Multiset.card (innerCrit K σ) := by
    rw [hL, List.length_reverse, Multiset.length_sort]
  have hmem : x ∈ L := by
    rw [hL, List.mem_reverse, Multiset.mem_sort]; exact hx
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hmem
  refine ⟨i + 1, by omega, by omega, ?_⟩
  unfold xCrit
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  simp only [Nat.add_sub_cancel]
  rw [← hL, List.getD_eq_getElem _ _ hi, hix]

/-- Two finite `x_j = x_l` with `f''(x_l) ≠ 0` have the same index. -/
private lemma qc_xCrit_inj (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {j l : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 2 * numBands K σ)
    (hl1 : 1 ≤ l) (hl : l ≤ 2 * numBands K σ)
    (hfj : ¬ (j = 2 * numBands K σ ∧ yEdge K σ = 0))
    (hfl : ¬ (l = 2 * numBands K σ ∧ yEdge K σ = 0))
    (heq : xCrit K σ j = xCrit K σ l) (h2 : fR2 K σ (xCrit K σ l) ≠ 0) : j = l := by
  have hc := (card_innerCrit K σ hσ hK hS).1
  by_contra hjl
  rcases lt_or_eq_of_le hj with hjlt | hjeq <;> rcases lt_or_eq_of_le hl with hllt | hleq
  · -- both inner: a double point of `𝒞`
    obtain ⟨hmem, -⟩ := qc_xCrit_spec K σ hσ hK hS hl1 hllt
    obtain ⟨hin, hnp, hf1⟩ := qc_mem_innerCrit K σ hσ hK hmem
    have hcount := count_innerCrit K σ hσ hK hin (fun s hs h0 => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
      exact hnp i (hi ▸ h0))
    rw [ite_eq_left_of_eq_true _ _ (eq_true hf1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
      at hcount
    set L := ((innerCrit K σ).sort (· ≤ ·)).reverse with hL
    have hlen : L.length = Multiset.card (innerCrit K σ) := by
      rw [hL, List.length_reverse, Multiset.length_sort]
    have hxj : xCrit K σ j = L[j - 1]'(by omega) := by
      unfold xCrit
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), ← hL,
        List.getD_eq_getElem _ _ (by omega)]
    have hxl : xCrit K σ l = L[l - 1]'(by omega) := by
      unfold xCrit
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), ← hL,
        List.getD_eq_getElem _ _ (by omega)]
    have hdup : L.Duplicate (xCrit K σ l) := by
      rw [List.duplicate_iff_exists_distinct_get]
      rcases lt_or_gt_of_ne hjl with hlt | hgt
      · exact ⟨⟨j - 1, by omega⟩, ⟨l - 1, by omega⟩, by
          show j - 1 < l - 1; omega, by rw [← heq, hxj]; rfl, by rw [hxl]; rfl⟩
      · exact ⟨⟨l - 1, by omega⟩, ⟨j - 1, by omega⟩, by
          show l - 1 < j - 1; omega, by rw [hxl]; rfl, by rw [← heq, hxj]; rfl⟩
    rw [List.duplicate_iff_two_le_count] at hdup
    have : L.count (xCrit K σ l) = (innerCrit K σ).count (xCrit K σ l) := by
      rw [hL, List.count_reverse, ← Multiset.coe_count, Multiset.sort_eq]
    omega
  · -- `l = 2p`: `x_l` is not in the inner region
    have hy0 : yEdge K σ ≠ 0 := fun h0 => hfl ⟨hleq, h0⟩
    obtain ⟨hch, -⟩ := yEdge_spec K σ hσ hK hS
    have hx : xCrit K σ l = (yEdge K σ)⁻¹ := by
      unfold xCrit; rw [ite_eq_left_iff.mpr (fun h => absurd hleq h)]
    obtain ⟨hmem, -⟩ := qc_xCrit_spec K σ hσ hK hS hj1 hjlt
    obtain ⟨hin, -, -⟩ := qc_mem_innerCrit K σ hσ hK hmem
    rw [heq, hx] at hin
    exact qc_inv_not_inner hy0 hch hin
  · have hy0 : yEdge K σ ≠ 0 := fun h0 => hfj ⟨hjeq, h0⟩
    obtain ⟨hch, -⟩ := yEdge_spec K σ hσ hK hS
    have hx : xCrit K σ j = (yEdge K σ)⁻¹ := by
      unfold xCrit; rw [ite_eq_left_iff.mpr (fun h => absurd hjeq h)]
    obtain ⟨hmem, -⟩ := qc_xCrit_spec K σ hσ hK hS hl1 hllt
    obtain ⟨hin, -, -⟩ := qc_mem_innerCrit K σ hσ hK hmem
    rw [← heq, hx] at hin
    exact qc_inv_not_inner hy0 hch hin
  · exact hjl (hjeq.trans hleq.symm)

/-! ## The partner of a regular edge at `N − 1` -/

private lemma qc_neg_one_pow_ne {k l : ℕ} (h : l % 2 ≠ k % 2) :
    (-1 : ℝ) ^ (l + 1) = -((-1 : ℝ) ^ (k + 1)) := by
  rw [pow_succ, pow_succ, neg_one_pow_eq_pow_mod_two (n := l),
    neg_one_pow_eq_pow_mod_two (n := k)]
  rcases Nat.mod_two_eq_zero_or_one l with hl | hl <;>
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · omega
  · rw [hl, hk]; norm_num
  · rw [hl, hk]; norm_num
  · omega

/-- The critical point `ẋ = x_k + ε t*` of `f_{N−1}` in the window around a regular `x_k`:
`0 ≤ t* ≤ A₀/N`, `f'_{N−1}(ẋ) = 0`, `ε f''_{N−1}(ẋ) > 0`, and `t*` is the only zero of
`t ↦ f'_{N−1}(x_k + ε t)` on `|t| ≤ ρ₁`. -/
private lemma qc_pw {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) (hN2 : 2 ≤ N)
    (hNa : 2 * (32 / (3 * edgec2 τ * edgecx τ ^ 2)) / edgeRho1 τ ≤ N)
    (hNc : 64 / (3 * edgec2 τ * edgecx τ ^ 3) < N) :
    ∃ ts, 0 ≤ ts ∧ ts ≤ 32 / (3 * edgec2 τ * edgecx τ ^ 2) / N ∧
      fR1 (N - 1) σ (xCrit N σ k + (-1 : ℝ) ^ (k + 1) * ts) = 0 ∧
      0 < (-1 : ℝ) ^ (k + 1) * fR2 (N - 1) σ (xCrit N σ k + (-1 : ℝ) ^ (k + 1) * ts) ∧
      ∀ t, |t| ≤ edgeRho1 τ → fR1 (N - 1) σ (xCrit N σ k + (-1 : ℝ) ^ (k + 1) * t) = 0 →
        t = ts := by
  have hτ := h.pos
  obtain ⟨hcx, hc2, hC3, hρ, hρ10, hρ0c, hρ0τ, hC3ρ⟩ := qc_edge_consts hτ
  set cx := edgecx τ with hcxdef
  set c2 := edgec2 τ with hc2def
  set ρ := edgeRho1 τ with hρdef
  set A₀ := 32 / (3 * c2 * cx ^ 2) with hA₀
  have hA₀0 : 0 < A₀ := by positivity
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  set x := xCrit N σ k with hxdef
  set ε := (-1 : ℝ) ^ (k + 1) with hεdef
  have hεa : |ε| = 1 := qc_sign_abs k
  have hwin : ∀ t, |t| ≤ ρ → _ := fun t ht => qc_win_N h hk ht
  set t₀ := A₀ / N with ht₀
  have ht₀0 : 0 < t₀ := by positivity
  have ht₀ρ : t₀ ≤ ρ / 2 := by
    rw [ht₀, div_le_iff₀ hN0]
    rw [div_le_iff₀ hρ] at hNa; linarith
  set G : ℝ → ℝ := fun t => fR1 (N - 1) σ (x + ε * t) with hG
  have hGe : ∀ t, ((N : ℝ) - 1) * G t = N * fR1 N σ (x + ε * t) - ((x + ε * t) ^ 2)⁻¹ :=
    fun t => qc_fR1_pred σ hN2 _
  have hy2 : ∀ t, |t| ≤ ρ → ((x + ε * t) ^ 2)⁻¹ ≤ 4 / cx ^ 2 := by
    intro t ht
    obtain ⟨⟨-, -, hya⟩, -⟩ := hwin t ht
    rw [← sq_abs]
    calc (|x + ε * t| ^ 2)⁻¹ ≤ ((cx / 2) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hya 2)
      _ = 4 / cx ^ 2 := by field_simp; ring
  have hG1 : ∀ t, -ρ ≤ t → t ≤ 0 → G t < 0 := by
    intro t ht1 ht2
    have ht : |t| ≤ ρ := abs_le.2 ⟨ht1, by linarith⟩
    obtain ⟨⟨hy0, -, -⟩, -, -, hC', -, -⟩ := hwin t ht
    have h3 := hC' ht2
    have h4 : 0 < ((x + ε * t) ^ 2)⁻¹ := by positivity
    have h3' : (N : ℝ) * fR1 N σ (x + ε * t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hN0.le
        (h3.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht2))
    have h5 : ((N : ℝ) - 1) * G t < 0 := by
      rw [hGe]; linarith
    exact neg_of_mul_neg_right h5 hN1.le
  have hG2 : 0 < G t₀ := by
    have ht : |t₀| ≤ ρ := abs_le.2 ⟨by linarith, by linarith⟩
    obtain ⟨-, -, hC, -, -, -⟩ := hwin t₀ ht
    have h3 := hC ht₀0.le
    have h4 := hy2 t₀ ht
    have h5 : 8 / cx ^ 2 ≤ N * fR1 N σ (x + ε * t₀) := by
      have : (N : ℝ) * (3 * c2 / 4 * t₀) = 8 / cx ^ 2 := by
        rw [ht₀, hA₀]; field_simp; ring
      rw [← this]
      exact mul_le_mul_of_nonneg_left h3 hN0.le
    have h6 : 0 < ((N : ℝ) - 1) * G t₀ := by
      rw [hGe]
      have : 4 / cx ^ 2 < 8 / cx ^ 2 := by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num
      linarith
    exact pos_of_mul_pos_right h6 hN1.le
  have hN3 : 16 / cx ^ 3 < N * (3 * c2 / 4) := by
    rw [div_lt_iff₀ (by positivity)] at hNc
    rw [div_lt_iff₀ (by positivity)]
    have e : (N : ℝ) * (3 * c2 / 4) * cx ^ 3 = N * (3 * c2 * cx ^ 3) / 4 := by ring
    rw [e]; linarith
  have hG3 : ∀ t, |t| ≤ ρ → 0 < ε * fR2 (N - 1) σ (x + ε * t) := by
    intro t ht
    obtain ⟨⟨hy0, -, hya⟩, hB2, -⟩ := hwin t ht
    have e := qc_fR2_pred σ hN2 (x + ε * t)
    have hy3 : |2 * ε * ((x + ε * t) ^ 3)⁻¹| ≤ 16 / cx ^ 3 := by
      rw [abs_mul, abs_mul, hεa, abs_inv, abs_pow, abs_two]
      calc 2 * 1 * (|x + ε * t| ^ 3)⁻¹ ≤ 2 * 1 * ((cx / 2) ^ 3)⁻¹ := by
            gcongr
        _ = 16 / cx ^ 3 := by field_simp; ring
    have hmain : N * (3 * c2 / 4) ≤ ε * (N * fR2 N σ (x + ε * t)) := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hB2 hN0.le
    have h6 := (abs_le.1 hy3).1
    have h5 : 0 < ((N : ℝ) - 1) * (ε * fR2 (N - 1) σ (x + ε * t)) := by
      have e3 : ((N : ℝ) - 1) * (ε * fR2 (N - 1) σ (x + ε * t)) =
          ε * (N * fR2 N σ (x + ε * t)) + 2 * ε * ((x + ε * t) ^ 3)⁻¹ := by
        rw [mul_left_comm, e]; ring
      rw [e3]
      linarith only [hmain, h6, hN3]
    exact pos_of_mul_pos_right h5 hN1.le
  have hGd : ∀ t, |t| ≤ ρ → HasDerivAt G (fR2 (N - 1) σ (x + ε * t) * ε) t := by
    intro t ht
    obtain ⟨⟨hy0, hynp, -⟩, -⟩ := hwin t ht
    have h3 : HasDerivAt (fun t : ℝ => x + ε * t) ε t := by
      simpa using ((hasDerivAt_id t).const_mul ε).const_add x
    exact (hasDerivAt_fR1 (N - 1) σ hy0 hynp).comp t h3
  have hGmono : StrictMonoOn G (Set.Icc (-ρ) ρ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ fun t ht => ?_
    · intro t ht
      exact (hGd t (abs_le.2 ⟨ht.1, ht.2⟩)).continuousAt.continuousWithinAt
    · rw [interior_Icc] at ht
      rw [(hGd t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)).deriv, mul_comm]
      exact hG3 t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
  have hGcont : ContinuousOn G (Set.Icc 0 t₀) := fun t ht =>
    (hGd t (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)).continuousAt.continuousWithinAt
  obtain ⟨ts, hts, hGts⟩ := intermediate_value_Icc ht₀0.le hGcont
    ⟨(hG1 0 (by linarith) le_rfl).le, hG2.le⟩
  have htsρ : |ts| ≤ ρ := abs_le.2 ⟨by linarith [hts.1], by linarith [hts.2]⟩
  refine ⟨ts, hts.1, hts.2, hGts, hG3 ts htsρ, fun t ht hGt => ?_⟩
  exact hGmono.injOn ⟨(abs_le.1 ht).1, (abs_le.1 ht).2⟩
    ⟨(abs_le.1 htsρ).1, (abs_le.1 htsρ).2⟩ (hGt.trans hGts.symm)

/-- `A₀ = 32/(3 c₂ c_x²)`: the window `t* ≤ A₀/N` at `N − 1`. -/
private def qcA0 (τ : ℝ) : ℝ := 32 / (3 * edgec2 τ * edgecx τ ^ 2)

/-- The shift constant `C₁` of `edge_pred`. -/
private def qcC1 (τ : ℝ) : ℝ :=
  2 * ((edgeC2 τ / 2 + edgec2 τ / 4) * qcA0 τ ^ 2 + 2 * τ⁻¹ * (1 + τ⁻¹) + 2 / edgecx τ) + 1

private lemma qc_C1_pos {τ : ℝ} (hτ : 0 < τ) : 0 < qcC1 τ ∧ 0 < qcA0 τ := by
  obtain ⟨hcx, hc2, -⟩ := qc_edge_consts hτ
  have hC2 : 0 ≤ edgeC2 τ := by
    have := Real.sqrt_pos.2 hτ
    unfold edgeC2 edgecx edgeCx; positivity
  have hA : 0 < qcA0 τ := by unfold qcA0; positivity
  refine ⟨?_, hA⟩
  unfold qcC1
  have : 0 < τ⁻¹ := inv_pos.mpr hτ
  positivity

/-- The shift `|ȧ − a_k| ≤ C₁/N` at the critical point `ẋ = x_k + ε t*`, `t* ≤ A₀/N`. -/
private lemma qc_pshift {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) (hN2 : 2 ≤ N) {ts : ℝ} (hts0 : 0 ≤ ts)
    (hts : ts ≤ qcA0 τ / N) (htsρ : ts ≤ edgeRho1 τ) :
    |fR (N - 1) σ (xCrit N σ k + (-1 : ℝ) ^ (k + 1) * ts) - edgeVal N σ k| ≤ qcC1 τ / N := by
  have hτ := h.pos
  obtain ⟨hcx, hc2, -⟩ := qc_edge_consts hτ
  obtain ⟨hC1, hA0⟩ := qc_C1_pos hτ
  have hC2 : 0 ≤ edgeC2 τ := by
    have := Real.sqrt_pos.2 hτ
    unfold edgeC2 edgecx edgeCx; positivity
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hK : 0 < N := by omega
  obtain ⟨hk1, hk2, -⟩ := id hk
  set x := xCrit N σ k
  set ε := (-1 : ℝ) ^ (k + 1)
  set xd := x + ε * ts with hxd
  have htsa : |ts| ≤ edgeRho1 τ := by rw [abs_of_nonneg hts0]; exact htsρ
  obtain ⟨⟨hxd0, hxdnp, hxda⟩, -, -, -, -, hfxd⟩ := qc_win_N h hk htsa
  set Ct := edgeC2 τ / 2 + edgec2 τ / 4 with hCt
  have hCt0 : 0 ≤ Ct := by positivity
  set C' := Ct * qcA0 τ ^ 2 + 2 * τ⁻¹ * (1 + τ⁻¹) + 2 / edgecx τ with hC'
  have hC1e : qcC1 τ = 2 * C' + 1 := rfl
  have e := qc_fR_pred σ hN2 xd
  have e2 : fR (N - 1) σ xd - edgeVal N σ k =
      (N * (fR N σ xd - edgeVal N σ k) + (edgeVal N σ k + xd⁻¹)) / ((N : ℝ) - 1) := by
    rw [eq_div_iff hN1.ne']; linear_combination e
  rw [e2, abs_div, abs_of_pos hN1]
  have h3 : |fR N σ xd - edgeVal N σ k| ≤ Ct * (qcA0 τ / N) ^ 2 := by
    refine hfxd.trans (mul_le_mul_of_nonneg_left ?_ hCt0)
    exact pow_le_pow_left₀ hts0 hts 2
  have h4 : |xd⁻¹| ≤ 2 / edgecx τ := by
    rw [abs_inv]
    calc |xd|⁻¹ ≤ (edgecx τ / 2)⁻¹ := inv_anti₀ (by positivity) hxda
      _ = 2 / edgecx τ := by field_simp
  obtain ⟨hak0, hakC⟩ := qc_edge_nonneg h hK hk1 hk2
  have h5 : |N * (fR N σ xd - edgeVal N σ k) + (edgeVal N σ k + xd⁻¹)| ≤ C' := by
    calc |N * (fR N σ xd - edgeVal N σ k) + (edgeVal N σ k + xd⁻¹)|
        ≤ N * |fR N σ xd - edgeVal N σ k| + (|edgeVal N σ k| + |xd⁻¹|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ (abs_add_le _ _))
          rw [abs_mul, Nat.abs_cast]
      _ ≤ N * (Ct * (qcA0 τ / N) ^ 2) + (2 * τ⁻¹ * (1 + τ⁻¹) + 2 / edgecx τ) := by
          rw [abs_of_nonneg hak0]
          gcongr
      _ ≤ C' := by
          have : (N : ℝ) * (Ct * (qcA0 τ / N) ^ 2) = Ct * qcA0 τ ^ 2 / N := by field_simp
          rw [this, hC']
          have : Ct * qcA0 τ ^ 2 / N ≤ Ct * qcA0 τ ^ 2 :=
            div_le_self (by positivity) (by linarith)
          linarith
  rw [div_le_div_iff₀ hN1 hN0, hC1e]
  have hC'0 : 0 ≤ C' := by positivity
  have : C' * N ≤ (2 * C' + 1) * (N - 1) := by nlinarith
  nlinarith [abs_nonneg (N * (fR N σ xd - edgeVal N σ k) + (edgeVal N σ k + xd⁻¹))]

/-- The index `l` of the critical point `ẋ` of `f_{N−1}` near a regular `x_k`: `l = 2p̃` when
`k = 2p`, and `l < 2p̃` when `k < 2p`. -/
private lemma qc_pindex {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) (hN2 : 2 ≤ N) {xd : ℝ}
    (hd : |xd - xCrit N σ k| < τ / 2) (hdc : |xd - xCrit N σ k| ≤ edgecx τ / 2)
    (hxd0 : xd ≠ 0) (hnp : ∀ i, 1 + σ i * xd ≠ 0) (hcrit : fR1 (N - 1) σ xd = 0) :
    ∃ l, 1 ≤ l ∧ l ≤ 2 * numBands (N - 1) σ ∧
      ¬ (l = 2 * numBands (N - 1) σ ∧ yEdge (N - 1) σ = 0) ∧ xCrit (N - 1) σ l = xd ∧
      (k = 2 * numBands N σ → l = 2 * numBands (N - 1) σ) ∧
      (k < 2 * numBands N σ → l < 2 * numBands (N - 1) σ) := by
  have hτ := h.pos
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have hp1 := card_innerCrit (N - 1) σ hσ hK1 hS
  obtain ⟨hk1, hk2, hka, -, hpole⟩ := id hk
  have hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) := by
    rintro ⟨hk', hy⟩
    have : edgeVal N σ k = 0 := by
      unfold edgeVal; simp [hk', hy, FChart]
    linarith
  have hmarg := hpole hfin
  obtain ⟨hxl, -, -⟩ := xCrit_bounds h hk
  set x := xCrit N σ k with hxdef
  by_cases hkp : k = 2 * numBands N σ
  · -- the bottom edge: `x_{2p} = 1/y_{2p}`
    have hy0 : yEdge N σ ≠ 0 := fun h0 => hfin ⟨hkp, h0⟩
    obtain ⟨hch, -⟩ := yEdge_spec N σ hσ hK hS
    have hx : x = (yEdge N σ)⁻¹ := by
      rw [hxdef]; unfold xCrit; rw [ite_eq_left_iff.mpr (fun h => absurd hkp h)]
    have hx0 : x ≠ 0 := by rw [hx]; exact inv_ne_zero hy0
    have hchd : InChart σ xd⁻¹ := by
      intro s hs
      have hs0 := qc_pos_of_mem hs
      have ha : 0 < x⁻¹ + s := by rw [hx, inv_inv]; exact hch s hs
      have hm := hmarg s hs
      set u := 1 + s * x
      set u' := 1 + s * xd
      have hu : |u| = s * |x + s⁻¹| := by
        have : u = s * (x + s⁻¹) := by simp only [u]; field_simp; ring
        rw [this, abs_mul, abs_of_pos hs0]
      have huu : 0 < u * u' := by
        have h1 : |u' - u| < |u| := by
          have : u' - u = s * (xd - x) := by simp only [u, u']; ring
          rw [this, abs_mul, abs_of_pos hs0, hu]
          have : |xd - x| < |x + s⁻¹| := by linarith
          exact mul_lt_mul_of_pos_left this hs0
        rcases lt_or_gt_of_ne (show u ≠ 0 by
          intro h0; rw [h0, abs_zero] at h1; exact absurd h1 (not_lt.mpr (abs_nonneg _)))
          with hneg | hpos
        · rw [abs_of_neg hneg] at h1
          have := (abs_lt.1 h1).2
          nlinarith
        · rw [abs_of_pos hpos] at h1
          have := (abs_lt.1 h1).1
          nlinarith
      have hxx : 0 < x * xd := by
        have h1 : |xd - x| < |x| := by
          have := abs_pos.2 hx0
          linarith
        rcases lt_or_gt_of_ne hx0 with hneg | hpos
        · rw [abs_of_neg hneg] at h1
          have := (abs_lt.1 h1).2
          nlinarith
        · rw [abs_of_pos hpos] at h1
          have := (abs_lt.1 h1).1
          nlinarith
      have hux : 0 < u * x := by
        have e : x⁻¹ + s = u / x := by simp only [u]; field_simp
        rw [e] at ha
        rcases lt_or_gt_of_ne hx0 with hneg | hpos
        · have := (div_pos_iff.1 ha)
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · nlinarith
        · have := (div_pos_iff.1 ha)
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · nlinarith
          · linarith
      have hud : 0 < u' * xd := by
        have : 0 < (u' * xd) * (u * x) := by
          have e : (u' * xd) * (u * x) = (u * u') * (x * xd) := by ring
          rw [e]; positivity
        exact pos_of_mul_pos_left this hux.le
      have e : xd⁻¹ + s = u' / xd := by simp only [u']; field_simp
      rw [e]
      rcases lt_or_gt_of_ne hxd0 with hneg | hpos
      · have : u' < 0 := by nlinarith
        exact div_pos_of_neg_of_neg this hneg
      · have : 0 < u' := by nlinarith
        exact div_pos this hpos
    have hF : FChart1 (N - 1) σ xd⁻¹ = 0 := by
      have e := qc_fR1_inv (N - 1) σ hσ (inv_ne_zero hxd0) hchd
      rw [inv_inv, hcrit] at e
      have h2 : (xd⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hxd0)
      have h3 : (xd⁻¹) ^ 2 * FChart1 (N - 1) σ xd⁻¹ = 0 := by linarith
      exact (mul_eq_zero.mp h3).resolve_left h2
    have hy1 : yEdge (N - 1) σ = xd⁻¹ :=
      (existsUnique_yEdge (N - 1) σ hσ hK1 hS).unique (yEdge_spec (N - 1) σ hσ hK1 hS)
        ⟨hchd, hF⟩
    refine ⟨2 * numBands (N - 1) σ, by omega, le_rfl, fun h' => inv_ne_zero hxd0
      (hy1 ▸ h'.2), ?_, fun _ => rfl, fun h' => absurd hkp (by omega)⟩
    unfold xCrit
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), hy1, inv_inv]
  · -- an inner edge
    have hklt : k < 2 * numBands N σ := lt_of_le_of_ne hk2 hkp
    obtain ⟨hmem, -⟩ := qc_xCrit_spec N σ hσ hK hS hk1 hklt
    obtain ⟨⟨hxneg, s, hs, hsx⟩, -, -⟩ := qc_mem_innerCrit N σ hσ hK hmem
    have hs0 := qc_pos_of_mem hs
    have hxdneg : xd < 0 := by
      rw [abs_of_neg hxneg] at hxl
      have := (abs_le.1 hdc).2
      have : edgecx τ / 2 > 0 := by
        obtain ⟨hcx, -⟩ := qc_edge_consts hτ; positivity
      linarith
    have hsxd : 0 < 1 + s * xd := by
      have hm := hmarg s hs
      have e1 : 1 + s * x = s * (x + s⁻¹) := by field_simp; ring
      have h1 : 0 < x + s⁻¹ := by
        rw [e1] at hsx; exact pos_of_mul_pos_right hsx hs0.le
      rw [abs_of_pos h1] at hm
      have e2 : 1 + s * xd = s * (xd + s⁻¹) := by field_simp; ring
      rw [e2]
      have := (abs_lt.1 hd).1
      have : 0 < xd + s⁻¹ := by linarith
      positivity
    have hin : xd ∈ innerCrit (N - 1) σ :=
      qc_innerCrit_of (N - 1) σ hσ ⟨hxdneg, s, hs, hsxd⟩ hnp hcrit
    obtain ⟨l, hl1, hl2, hxl'⟩ := qc_exists_index (N - 1) σ hσ hK1 hS hin
    exact ⟨l, hl1, hl2.le, fun h' => by omega, hxl', fun h' => absurd h' hkp, fun _ => hl2⟩

/-- On the gap side of a regular `a_k`, `m_N(g + i0) = x_k + ε t` with `0 < t < ρ₁`. -/
private lemma qc_gap_side_inv {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) {g : ℝ} (hg0 : 0 < g)
    (hgv : 0 < (-1 : ℝ) ^ (k + 1) * (g - edgeVal N σ k))
    (hgδ : (-1 : ℝ) ^ (k + 1) * (g - edgeVal N σ k) < edgec2 τ * edgeRho1 τ ^ 2 / 4) :
    ∃ t, 0 < t ∧ t ≤ edgeRho1 τ ∧
      mExt N σ g = ((xCrit N σ k + (-1 : ℝ) ^ (k + 1) * t : ℝ) : ℂ) := by
  have hτ := h.pos
  have hσ := h.nonneg
  have hK : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso; have := h.phi_lower; simp [phiRatio, h0] at this; linarith
    · exact h0
  obtain ⟨hcx, hc2, hC3, hρ, -⟩ := qc_edge_consts hτ
  set x := xCrit N σ k
  set ε := (-1 : ℝ) ^ (k + 1)
  have hε2 : ε * ε = 1 := by rw [← sq]; exact qc_sign_sq k
  set ρ := edgeRho1 τ
  have hwin : ∀ t, |t| ≤ ρ → _ := fun t ht => qc_win_N h hk ht
  set F : ℝ → ℝ := fun t => ε * (fR N σ (x + ε * t) - edgeVal N σ k) with hF
  have hF0 : F 0 = 0 := by
    obtain ⟨-, -, -, -, -, h6⟩ := hwin 0 (by simp; exact hρ.le)
    have h7 : fR N σ (x + ε * 0) - edgeVal N σ k = 0 :=
      abs_nonpos_iff.mp (h6.trans (by simp))
    simp only [hF]
    rw [h7, mul_zero]
  have hFρ : edgec2 τ * ρ ^ 2 / 4 ≤ F ρ := by
    obtain ⟨-, -, -, -, h5, -⟩ := hwin ρ (by rw [abs_of_pos hρ])
    have : edgec2 τ * ρ ^ 2 / 4 = edgec2 τ / 4 * ρ ^ 2 := by ring
    rw [this]; exact h5
  have hcont : ContinuousOn F (Set.Icc 0 ρ) := by
    intro t ht
    have ht' : |t| ≤ ρ := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨⟨hy0, hynp, -⟩, -⟩ := hwin t ht'
    have hc : ContinuousAt (fun t : ℝ => x + ε * t) t := by fun_prop
    have hcomp : ContinuousAt (fun t : ℝ => fR N σ (x + ε * t)) t :=
      ContinuousAt.comp (f := fun t : ℝ => x + ε * t) (hasDerivAt_fR N σ hy0 hynp).continuousAt hc
    exact (continuousAt_const.mul (hcomp.sub continuousAt_const)).continuousWithinAt
  have hmem : ε * (g - edgeVal N σ k) ∈ Set.Icc (F 0) (F ρ) :=
    ⟨by rw [hF0]; exact hgv.le, (le_of_lt hgδ).trans hFρ⟩
  obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc hρ.le hcont hmem
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · have : F t = F 0 := by rw [← h0]
      rw [hF0, hFt] at this
      linarith
    · exact h0
  have ht' : |t| ≤ ρ := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨⟨hy0, hynp, -⟩, -, hC, -⟩ := hwin t ht'
  have hfg : fR N σ (x + ε * t) = g := by
    have hFt' : ε * (fR N σ (x + ε * t) - edgeVal N σ k) = ε * (g - edgeVal N σ k) := hFt
    have := congrArg (ε * ·) hFt'
    simp only [← mul_assoc, hε2, one_mul] at this
    linarith
  have hd : 0 < fR1 N σ (x + ε * t) := by
    have := hC ht0.le
    have : 0 < 3 * edgec2 τ / 4 * t := by positivity
    linarith
  refine ⟨t, ht0, ht.2, ?_⟩
  have := mExt_fR_of_pos N σ hσ hK hy0 hynp (by rw [hfg]; exact hg0.ne') hd
  rw [hfg] at this
  exact this

/-- Separation at `N − 1`: every other edge of `N − 1` is at distance `≥ τ/2` from the partner. -/
private lemma qc_psep {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ} (h : DensityAssumptions τ N σ)
    (hk : RegularEdge τ N σ k) (hN2 : 2 ≤ N) {ts : ℝ}
    (huniq : ∀ t, |t| ≤ edgeRho1 τ →
      fR1 (N - 1) σ (xCrit N σ k + (-1 : ℝ) ^ (k + 1) * t) = 0 → t = ts)
    {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * numBands (N - 1) σ)
    (hlfin : ¬ (l = 2 * numBands (N - 1) σ ∧ yEdge (N - 1) σ = 0))
    (hxl : xCrit (N - 1) σ l = xCrit N σ k + (-1 : ℝ) ^ (k + 1) * ts)
    (hf2 : fR2 (N - 1) σ (xCrit (N - 1) σ l) ≠ 0)
    (hal : 3 * τ / 4 ≤ edgeVal (N - 1) σ l)
    (hsh : |edgeVal (N - 1) σ l - edgeVal N σ k| ≤ τ / 4)
    {D : ℝ} (hDτ : D ≤ τ / 8) (hDδ : D < edgec2 τ * edgeRho1 τ ^ 2 / 4)
    (hnear : ∀ j, 1 ≤ j → j ≤ 2 * numBands (N - 1) σ → τ / 4 ≤ edgeVal (N - 1) σ j →
      ∃ g, 0 < g ∧ g ∉ (varrho N σ).support ∧ mExt N σ g = xCrit (N - 1) σ j ∧
        |g - edgeVal (N - 1) σ j| ≤ τ / 8 ∧
        ∃ e, 1 ≤ e ∧ e ≤ 2 * numBands N σ ∧ |edgeVal N σ e - g| < D) :
    ∀ j, 1 ≤ j → j ≤ 2 * numBands (N - 1) σ → j ≠ l →
      τ / 2 ≤ |edgeVal (N - 1) σ l - edgeVal (N - 1) σ j| := by
  have hτ := h.pos
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  obtain ⟨hk1, hk2, hka, hsep, -⟩ := id hk
  intro j hj1 hj hjl
  by_contra hlt
  push Not at hlt
  have hajτ : τ / 4 ≤ edgeVal (N - 1) σ j := by
    have := (abs_lt.1 hlt).2
    linarith
  obtain ⟨g, hg0, hgns, hmg, hgj, e, he1, he2, heg⟩ := hnear j hj1 hj hajτ
  -- `e = k`
  have hek : e = k := by
    by_contra hne
    have := hsep e he1 he2 hne
    have h1 : |edgeVal N σ k - edgeVal N σ e| < τ := by
      have e1 : edgeVal N σ k - edgeVal N σ e = (edgeVal N σ k - edgeVal (N - 1) σ l) +
          (edgeVal (N - 1) σ l - edgeVal (N - 1) σ j) + (edgeVal (N - 1) σ j - g) +
          (g - edgeVal N σ e) := by ring
      calc |edgeVal N σ k - edgeVal N σ e|
          ≤ |edgeVal (N - 1) σ l - edgeVal N σ k| +
              |edgeVal (N - 1) σ l - edgeVal (N - 1) σ j| +
              |g - edgeVal (N - 1) σ j| + |edgeVal N σ e - g| := by
            rw [e1]
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
              (add_le_add ((abs_add_le _ _).trans (le_of_eq ?_)) (le_of_eq ?_))) (le_of_eq ?_))
            · rw [abs_sub_comm]
            · rw [abs_sub_comm]
            · rw [abs_sub_comm]
        _ < τ := by linarith
    linarith
  rw [hek] at heg
  -- the gap side
  set ε := (-1 : ℝ) ^ (k + 1) with hεdef
  have hgside : 0 < ε * (g - edgeVal N σ k) := by
    rcases Nat.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · -- `k = 2b`: lower edge, band `b` above
      have hε : ε = -1 := by
        rw [hεdef, hb, pow_succ, ← two_mul, pow_mul]; norm_num
      rw [hε]
      by_contra hc
      push Not at hc
      have hb1 : 1 ≤ b := by omega
      have hsep' := hsep (k - 1) (by omega) (by omega) (by omega)
      have hanti := qc_edge_anti N σ hσ hK hS (j := k - 1) (k := k) (by omega) (by omega) hk2
      rw [abs_of_nonpos (by linarith)] at hsep'
      have hmem : g ∈ (varrho N σ).support := by
        refine (mem_support_varrho_iff N σ hσ hK hS hg0).2 ⟨b, hb1, by omega, ?_, ?_⟩
        · rw [show 2 * b = k by omega]; linarith
        · rw [show 2 * b - 1 = k - 1 by omega]
          have := (abs_lt.1 heg).1
          linarith
      exact hgns hmem
    · -- `k = 2b + 1`: upper edge, band `b + 1` below
      have hε : ε = 1 := by
        rw [hεdef, hb, show 2 * b + 1 + 1 = 2 * (b + 1) by ring, pow_mul]; norm_num
      rw [hε]
      by_contra hc
      push Not at hc
      have hkp : k + 1 ≤ 2 * numBands N σ := by omega
      have hsep' := hsep (k + 1) (by omega) hkp (by omega)
      have hanti := qc_edge_anti N σ hσ hK hS (j := k) (k := k + 1) hk1 (by omega) hkp
      rw [abs_of_nonneg (by linarith)] at hsep'
      have hmem : g ∈ (varrho N σ).support := by
        refine (mem_support_varrho_iff N σ hσ hK hS hg0).2 ⟨b + 1, by omega, by omega, ?_, ?_⟩
        · rw [show 2 * (b + 1) = k + 1 by omega]
          have := (abs_lt.1 heg).2
          linarith
        · rw [show 2 * (b + 1) - 1 = k by omega]; linarith
      exact hgns hmem
  have hgδ : ε * (g - edgeVal N σ k) < edgec2 τ * edgeRho1 τ ^ 2 / 4 := by
    have : |ε * (g - edgeVal N σ k)| < D := by
      rw [abs_mul, qc_sign_abs, one_mul, abs_sub_comm]; exact heg
    exact lt_of_le_of_lt (le_abs_self _) (this.trans hDδ)
  obtain ⟨t, ht0, htρ, hmt⟩ := qc_gap_side_inv h hk hg0 hgside hgδ
  rw [hmg] at hmt
  have hxj : xCrit (N - 1) σ j = xCrit N σ k + ε * t := Complex.ofReal_injective hmt
  have hfinj : ¬ (j = 2 * numBands (N - 1) σ ∧ yEdge (N - 1) σ = 0) := by
    rintro ⟨hj', hy⟩
    have : edgeVal (N - 1) σ j = 0 := by
      unfold edgeVal; simp [hj', hy, FChart]
    linarith
  obtain ⟨-, -, hcj⟩ := qc_xCrit_crit (N - 1) σ hσ hK1 hS hj1 hj hfinj
  rw [hxj] at hcj
  have hts := huniq t (by rw [abs_of_pos ht0]; exact htρ) hcj
  have heq : xCrit (N - 1) σ j = xCrit (N - 1) σ l := by rw [hxj, hxl, hts]
  exact hjl (qc_xCrit_inj (N - 1) σ hσ hK1 hS hj1 hj hl1 hl2 hfinj hlfin heq hf2)

/-- An edge regular at `τ` for `N` has a partner edge of the same parity for `N − 1`, within
`C₁/N`, regular at `τ/2`. -/
theorem edge_pred (τ : ℝ) (hτ : 0 < τ) :
    ∃ C₁ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ k, RegularEdge τ N σ k → ∃ l, l % 2 = k % 2 ∧
        |edgeVal (N - 1) σ l - edgeVal N σ k| ≤ C₁ / N ∧ RegularEdge (τ / 2) (N - 1) σ l := by
  obtain ⟨hcx, hc2, hC3, hρ, hρ10, hρ0c, hρ0τ, hC3ρ⟩ := qc_edge_consts hτ
  obtain ⟨hC1, hA0⟩ := qc_C1_pos hτ
  set δ₀ := edgec2 τ * edgeRho1 τ ^ 2 / 4 with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  set D := min (δ₀ / 2) (τ / 8) with hDdef
  have hD0 : 0 < D := lt_min (by positivity) (by positivity)
  have hDτ : D ≤ τ / 8 := min_le_right _ _
  have hDδ : D < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨B, N₁, hnear⟩ := qc_edge_near τ (τ / 4) D hτ (by positivity) hD0 (by linarith)
  set Q := (N₁ : ℝ) + 2 * qcA0 τ / edgeRho1 τ + 4 * qcA0 τ / τ +
    64 / (3 * edgec2 τ * edgecx τ ^ 3) + 4 * qcC1 τ / τ + 8 * |B| / τ + 3 with hQ
  refine ⟨qcC1 τ, ⌈Q⌉₊, ?_⟩
  intro N hN M σ h k hk
  have hNQ : Q ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hp1 : 0 ≤ 2 * qcA0 τ / edgeRho1 τ := by positivity
  have hp2 : 0 ≤ 4 * qcA0 τ / τ := by positivity
  have hp3 : 0 ≤ 64 / (3 * edgec2 τ * edgecx τ ^ 3) := by positivity
  have hp4 : 0 ≤ 4 * qcC1 τ / τ := by positivity
  have hp5 : 0 ≤ 8 * |B| / τ := by positivity
  have hp6 : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
  have hNr : (3 : ℝ) ≤ N := by linarith
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  have hNN₁ : N₁ ≤ N := by exact_mod_cast (show (N₁ : ℝ) ≤ N by linarith)
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by linarith
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have h1 := qc_da_pred h hN2
  obtain ⟨hk1, hk2, hka, hsep, hpole⟩ := id hk
  have hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) := by
    rintro ⟨hk', hy⟩
    have : edgeVal N σ k = 0 := by
      unfold edgeVal; simp [hk', hy, FChart]
    linarith
  have hmarg := hpole hfin
  -- the critical point `ẋ` of `f_{N−1}`
  have hNa : 2 * (32 / (3 * edgec2 τ * edgecx τ ^ 2)) / edgeRho1 τ ≤ N := by
    have : 2 * qcA0 τ / edgeRho1 τ ≤ N := by linarith
    exact this
  have hNc : 64 / (3 * edgec2 τ * edgecx τ ^ 3) < N := by linarith
  obtain ⟨ts, hts0, hts, hcrit, hf2, huniq⟩ := qc_pw h hk hN2 hNa hNc
  have hts' : ts ≤ qcA0 τ / N := hts
  have hA0N : qcA0 τ / N ≤ edgeRho1 τ / 2 := by
    rw [div_le_iff₀ hN0]
    have : 2 * qcA0 τ / edgeRho1 τ ≤ N := by linarith
    rw [div_le_iff₀ hρ] at this; linarith
  have hA0τ : qcA0 τ / N ≤ τ / 4 := by
    rw [div_le_iff₀ hN0]
    have : 4 * qcA0 τ / τ ≤ N := by linarith
    rw [div_le_iff₀ hτ] at this; linarith
  have htsρ : ts ≤ edgeRho1 τ := by linarith
  set x := xCrit N σ k with hxdef
  set ε := (-1 : ℝ) ^ (k + 1) with hεdef
  set xd := x + ε * ts with hxd
  have htsa : |ts| ≤ edgeRho1 τ := by rw [abs_of_nonneg hts0]; exact htsρ
  obtain ⟨⟨hxd0, hxdnp, -⟩, -⟩ := qc_win_N h hk htsa
  have hdx : |xd - x| = ts := by
    rw [hxd, add_sub_cancel_left, abs_mul, qc_sign_abs, one_mul, abs_of_nonneg hts0]
  obtain ⟨l, hl1, hl2, hlfin, hxl, -, -⟩ := qc_pindex h hk hN2 (xd := xd)
    (by rw [hdx]; linarith) (by rw [hdx]; linarith) hxd0 hxdnp hcrit
  have hshift := qc_pshift h hk hN2 hts0 hts' htsρ
  have hal : edgeVal (N - 1) σ l = fR (N - 1) σ xd := by
    rw [edgeVal_eq_fR (N - 1) σ hσ hK1 hS hl1 hl2 hlfin, hxl]
  have hC1N : qcC1 τ / N ≤ τ / 4 := by
    rw [div_le_iff₀ hN0]
    have : 4 * qcC1 τ / τ ≤ N := by linarith
    rw [div_le_iff₀ hτ] at this; linarith
  have hsh : |edgeVal (N - 1) σ l - edgeVal N σ k| ≤ qcC1 τ / N := by rw [hal]; exact hshift
  have hal34 : 3 * τ / 4 ≤ edgeVal (N - 1) σ l := by
    have := (abs_le.1 hsh).1
    linarith
  have hf2' : fR2 (N - 1) σ (xCrit (N - 1) σ l) ≠ 0 := by
    rw [hxl]; intro h0; rw [h0, mul_zero] at hf2; exact lt_irrefl _ hf2
  have hBN : |B| / N ≤ τ / 8 := by
    rw [div_le_iff₀ hN0]
    have : 8 * |B| / τ ≤ N := by linarith
    rw [div_le_iff₀ hτ] at this; linarith
  have hnear' : ∀ j, 1 ≤ j → j ≤ 2 * numBands (N - 1) σ → τ / 4 ≤ edgeVal (N - 1) σ j →
      ∃ g, 0 < g ∧ g ∉ (varrho N σ).support ∧ mExt N σ g = xCrit (N - 1) σ j ∧
        |g - edgeVal (N - 1) σ j| ≤ τ / 8 ∧
        ∃ e, 1 ≤ e ∧ e ≤ 2 * numBands N σ ∧ |edgeVal N σ e - g| < D := by
    intro j hj1 hj hjτ
    obtain ⟨g, hg0, hgns, hmg, hgj, he⟩ := hnear N hNN₁ M σ h j hj1 hj hjτ
    refine ⟨g, hg0, hgns, hmg, hgj.trans ?_, he⟩
    exact (div_le_div_of_nonneg_right (le_abs_self B) hN0.le).trans hBN
  have hsepl := qc_psep h hk hN2 huniq hl1 hl2 hlfin hxl hf2' hal34 (hsh.trans hC1N) hDτ hDδ
    hnear'
  have hreg : RegularEdge (τ / 2) (N - 1) σ l := by
    refine ⟨hl1, hl2, by linarith, hsepl, fun _ s hs => ?_⟩
    rw [hxl]
    have hm := hmarg s hs
    have : |xd + s⁻¹| ≥ |x + s⁻¹| - |xd - x| := by
      have := abs_sub_abs_le_abs_sub (x + s⁻¹) (xd + s⁻¹)
      rw [show x + s⁻¹ - (xd + s⁻¹) = -(xd - x) by ring, abs_neg] at this
      linarith
    rw [hdx] at this
    linarith
  refine ⟨l, ?_, hsh, hreg⟩
  -- the parity, from the sign of `f''_{N−1}(ẋ)`
  by_contra hpar
  have hc := edgec2_le_fR2_xCrit h1 hreg
  rw [qc_neg_one_pow_ne hpar, hxl] at hc
  have hc0 := (qc_edge_consts (show 0 < τ / 2 by positivity)).2.1
  have : -(ε * fR2 (N - 1) σ xd) = -ε * fR2 (N - 1) σ xd := by ring
  linarith

/-! ## Under the edge hypothesis of Theorem 3.12, the partner index is `k` -/

/-- With every edge of `[1, 2p]` distinct from `a_k` by `≥ c > 0`: `#{j : a_j > a_k} = k − 1`. -/
private lemma qc_card_above {K : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K)
    (hS : (posVals σ).Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * numBands K σ) {c : ℝ}
    (hc : 0 < c)
    (hsep : ∀ l, 1 ≤ l → l ≤ 2 * numBands K σ → l ≠ k → c ≤ |edgeVal K σ k - edgeVal K σ l|) :
    ((Finset.Icc 1 (2 * numBands K σ)).filter (fun j => edgeVal K σ k < edgeVal K σ j)).card =
      k - 1 := by
  have : (Finset.Icc 1 (2 * numBands K σ)).filter (fun j => edgeVal K σ k < edgeVal K σ j) =
      Finset.Icc 1 (k - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hj⟩, hlt⟩
      refine ⟨hj1, ?_⟩
      by_contra hc'
      have := qc_edge_anti K σ hσ hK hS hk1 (show k ≤ j by omega) hj
      linarith
    · rintro ⟨hj1, hj⟩
      refine ⟨⟨hj1, by omega⟩, ?_⟩
      have h1 := qc_edge_anti K σ hσ hK hS hj1 (show j ≤ k by omega) hk
      have h2 := hsep j hj1 (by omega) (by omega)
      rw [abs_of_nonpos (by linarith)] at h2
      linarith
  rw [this, Nat.card_Icc]
  omega

/-- Under the edge hypothesis of Theorem 3.12 (every edge with `a_k ≥ τ/2` regular at `τ/2`), the
partner of each such edge has the same index. -/
theorem edge_pred_D6 (τ : ℝ) (hτ : 0 < τ) :
    ∃ C₁ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
        RegularEdge (τ / 2) N σ k) →
      ∀ k, 1 ≤ k → k ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ k →
        |edgeVal (N - 1) σ k - edgeVal N σ k| ≤ C₁ / N ∧ RegularEdge (τ / 4) (N - 1) σ k := by
  obtain ⟨C, N₂, hep⟩ := edge_pred (τ / 2) (by positivity)
  obtain ⟨B, N₃, hnear⟩ := qc_edge_near τ (τ / 4) (τ / 32) hτ (by positivity) (by positivity)
    (by linarith)
  set Q := (N₂ : ℝ) + N₃ + 32 * |C| / τ + 32 * |B| / τ + 3 with hQ
  refine ⟨C, ⌈Q⌉₊, ?_⟩
  intro N hN M σ h hD6 k hk1 hk2 hka
  have hNQ : Q ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hp1 : 0 ≤ 32 * |C| / τ := by positivity
  have hp2 : 0 ≤ 32 * |B| / τ := by positivity
  have hp3 : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
  have hp4 : (0 : ℝ) ≤ N₃ := Nat.cast_nonneg _
  have hNr : (3 : ℝ) ≤ N := by linarith
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  have hNN₂ : N₂ ≤ N := by exact_mod_cast (show (N₂ : ℝ) ≤ N by linarith)
  have hNN₃ : N₃ ≤ N := by exact_mod_cast (show (N₃ : ℝ) ≤ N by linarith)
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by linarith
  have hσ := h.nonneg
  have hS := qc_posVals_nonempty h
  have h2 := h.mono (show 0 < τ / 2 by positivity) (by linarith)
  have hCN : C / N ≤ τ / 32 := by
    rw [div_le_iff₀ hN0]
    have : 32 * |C| / τ ≤ N := by linarith
    rw [div_le_iff₀ hτ] at this
    linarith [le_abs_self C]
  have hBN : B / N ≤ τ / 32 := by
    rw [div_le_iff₀ hN0]
    have : 32 * |B| / τ ≤ N := by linarith
    rw [div_le_iff₀ hτ] at this
    linarith [le_abs_self B]
  -- the partners of the regular edges
  have hpart : ∀ j, 1 ≤ j → j ≤ 2 * numBands N σ → τ / 2 ≤ edgeVal N σ j →
      ∃ l, |edgeVal (N - 1) σ l - edgeVal N σ j| ≤ C / N ∧ RegularEdge (τ / 4) (N - 1) σ l := by
    intro j hj1 hj hja
    obtain ⟨l, -, hl1, hl2⟩ := hep N hNN₂ M σ h2 j (hD6 j hj1 hj hja)
    refine ⟨l, hl1, ?_⟩
    have : τ / 2 / 2 = τ / 4 := by ring
    rwa [this] at hl2
  obtain ⟨l, hlsh, hlreg⟩ := hpart k hk1 hk2 hka
  obtain ⟨hl1, hl2, hla, hlsep, hlmarg⟩ := hlreg
  obtain ⟨-, -, -, hksep, -⟩ := hD6 k hk1 hk2 hka
  -- `#{j : a_j > a_k} = k − 1` and `#{i : ȧ_i > ȧ_l} = l − 1`
  have hcS := qc_card_above hσ hK hS hk1 hk2 (c := τ / 2) (by positivity) hksep
  have hcT := qc_card_above hσ hK1 hS hl1 hl2 (c := τ / 4) (by positivity) hlsep
  set S := (Finset.Icc 1 (2 * numBands N σ)).filter (fun j => edgeVal N σ k < edgeVal N σ j)
  set T := (Finset.Icc 1 (2 * numBands (N - 1) σ)).filter
    (fun i => edgeVal (N - 1) σ l < edgeVal (N - 1) σ i)
  -- the map `S → T`, `j ↦ l_j`
  have hφ : ∀ j ∈ S, ∃ i ∈ T, |edgeVal (N - 1) σ i - edgeVal N σ j| ≤ C / N ∧
      RegularEdge (τ / 4) (N - 1) σ i := by
    intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hj⟩, hjk⟩ := hj
    have hja : τ / 2 ≤ edgeVal N σ j := by linarith
    obtain ⟨i, hish, hireg⟩ := hpart j hj1 hj hja
    obtain ⟨hi1, hi2, -⟩ := id hireg
    refine ⟨i, ?_, hish, hireg⟩
    simp only [T, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hi1, hi2⟩, ?_⟩
    have h1 := hksep j hj1 hj (by rintro rfl; exact lt_irrefl _ hjk)
    rw [abs_of_neg (by linarith)] at h1
    have := (abs_le.1 hish).1
    have := (abs_le.1 hlsh).2
    linarith
  choose! φ hφT hφsh hφreg using hφ
  have hφinj : Set.InjOn φ S := by
    intro j hj j' hj' heq
    by_contra hne
    simp only [S, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj hj'
    have h1 := (hD6 j hj.1.1 hj.1.2 (by linarith)).2.2.2.1 j' hj'.1.1 hj'.1.2 (Ne.symm hne)
    have a1 := hφsh j (by simpa [S] using hj)
    have a2 := hφsh j' (by simpa [S] using hj')
    rw [heq] at a1
    have : |edgeVal N σ j - edgeVal N σ j'| ≤ 2 * (C / N) := by
      calc |edgeVal N σ j - edgeVal N σ j'|
          ≤ |edgeVal (N - 1) σ (φ j') - edgeVal N σ j| +
              |edgeVal (N - 1) σ (φ j') - edgeVal N σ j'| := by
            have := abs_sub_le (edgeVal N σ j) (edgeVal (N - 1) σ (φ j')) (edgeVal N σ j')
            rwa [abs_sub_comm (edgeVal N σ j) (edgeVal (N - 1) σ (φ j'))] at this
        _ ≤ 2 * (C / N) := by linarith
    linarith
  have hST : S.card ≤ T.card := Finset.card_le_card_of_injOn φ (fun j hj => hφT j hj) hφinj
  -- the map `T → S`, `i ↦ e_i`
  have hψ : ∀ i ∈ T, ∃ e ∈ S, |edgeVal N σ e - edgeVal (N - 1) σ i| < τ / 16 := by
    intro i hi
    simp only [T, Finset.mem_filter, Finset.mem_Icc] at hi
    obtain ⟨⟨hi1, hi2⟩, hil⟩ := hi
    have hisep := hlsep i hi1 hi2 (by rintro rfl; exact lt_irrefl _ hil)
    rw [abs_of_neg (by linarith)] at hisep
    obtain ⟨g, -, -, -, hgi, e, he1, he2, heg⟩ := hnear N hNN₃ M σ h i hi1 hi2 (by linarith)
    have hei : |edgeVal N σ e - edgeVal (N - 1) σ i| < τ / 16 := by
      calc |edgeVal N σ e - edgeVal (N - 1) σ i|
          ≤ |edgeVal N σ e - g| + |g - edgeVal (N - 1) σ i| := abs_sub_le _ _ _
        _ < τ / 32 + τ / 32 := add_lt_add_of_lt_of_le heg (hgi.trans hBN)
        _ = τ / 16 := by ring
    refine ⟨e, ?_, hei⟩
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨he1, he2⟩, ?_⟩
    have := (abs_lt.1 hei).1
    have := (abs_le.1 hlsh).1
    linarith
  choose! ψ hψS hψd using hψ
  have hψinj : Set.InjOn ψ T := by
    have hkey : ∀ i ∈ T, i = φ (ψ i) := by
      intro i hi
      have hS' := hψS i hi
      have hd := hψd i hi
      have hsh := hφsh (ψ i) hS'
      obtain ⟨hr1, hr2, -, hrsep, -⟩ := hφreg (ψ i) hS'
      simp only [T, Finset.mem_filter, Finset.mem_Icc] at hi
      by_contra hne
      have := hrsep i hi.1.1 hi.1.2 hne
      have : |edgeVal (N - 1) σ (φ (ψ i)) - edgeVal (N - 1) σ i| < τ / 4 := by
        calc |edgeVal (N - 1) σ (φ (ψ i)) - edgeVal (N - 1) σ i|
            ≤ |edgeVal (N - 1) σ (φ (ψ i)) - edgeVal N σ (ψ i)| +
                |edgeVal N σ (ψ i) - edgeVal (N - 1) σ i| := abs_sub_le _ _ _
          _ < τ / 4 := by linarith
      linarith
    intro i hi i' hi' heq
    rw [hkey i hi, hkey i' hi', heq]
  have hTS : T.card ≤ S.card := Finset.card_le_card_of_injOn ψ (fun i hi => hψS i hi) hψinj
  have hlk : l = k := by omega
  subst hlk
  exact ⟨hlsh, hl1, hl2, hla, hlsep, hlmarg⟩

/-! ## The counts `n_{N−1}` and `n_N` against each other: a two-measure comparison -/

private lemma qc_cont_hor (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => mFun K σ (↑x + ↑y * Complex.I) :=
  (analyticOnNhd_mFun K σ hσ).continuousOn.comp_continuous (by fun_prop)
    fun x => by simpa [upperHalf] using hy

private lemma qc_cont_ver (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (E : ℝ) {η η₀ : ℝ}
    (hη : 0 < η) (hηη₀ : η ≤ η₀) :
    ContinuousOn (fun y : ℝ => mFun K σ (↑E + ↑y * Complex.I)) (Set.uIcc η η₀) := by
  refine (analyticOnNhd_mFun K σ hσ).continuousOn.comp (by fun_prop) fun y hy => ?_
  rw [Set.uIcc_of_le hηη₀] at hy
  simpa [upperHalf] using lt_of_lt_of_le hη hy.1

private lemma qc_integrable_decay (μ : Measure ℝ) [IsFiniteMeasure μ] (E η : ℝ) (hη : 0 < η) :
    Integrable (fun x : ℝ => η / (|x - E| + η)) μ := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun t => ?_)
  · exact (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    linarith [abs_nonneg (t - E)]

private lemma qc_integrable_arcdiff (μ : Measure ℝ) [IsFiniteMeasure μ] (E₁ E₂ y : ℝ) :
    Integrable (fun t : ℝ => Real.arctan ((E₂ - t) / y) - Real.arctan ((E₁ - t) / y)) μ := by
  refine Integrable.of_bound ?_ Real.pi (ae_of_all _ fun t => ?_)
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.arctan ((E₂ - t) / y) - Real.arctan ((E₁ - t) / y)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_le]
    constructor <;>
    linarith [Real.arctan_lt_pi_div_two ((E₂ - t) / y), Real.arctan_lt_pi_div_two ((E₁ - t) / y),
      Real.neg_pi_div_two_lt_arctan ((E₂ - t) / y), Real.neg_pi_div_two_lt_arctan ((E₁ - t) / y)]

/-- `n(E₁) − n(E₂) = K ϱ([E₁, E₂])` for `0 < E₂`, `E₁ ≤ E₂`. -/
private lemma qc_nClass_sub (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E₁ E₂ : ℝ}
    (h12 : E₁ ≤ E₂) (hE₂ : 0 < E₂) :
    nClass K σ E₁ - nClass K σ E₂ =
      K * ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho K σ) := by
  have hprob := isProbabilityMeasure_varrho K σ hσ hK
  have hI : ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho K σ) =
      (varrho K σ (Set.Icc E₁ E₂)).toReal := by
    simp [Measure.real]
  have hsplit := qc_Ici_split K σ h12
  have hIoi : varrho K σ (Set.Ioi E₂) = varrho K σ (Set.Ici E₂) := by
    refine le_antisymm (measure_mono Set.Ioi_subset_Ici_self) ?_
    calc varrho K σ (Set.Ici E₂) ≤ varrho K σ (Set.Ioi E₂ ∪ {E₂}) :=
          measure_mono fun t ht => by
            rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with h | h
            · exact Or.inr h.symm
            · exact Or.inl h
      _ ≤ varrho K σ (Set.Ioi E₂) + varrho K σ {E₂} := measure_union_le _ _
      _ = varrho K σ (Set.Ioi E₂) := by rw [qc_varrho_singleton K σ hE₂, add_zero]
  unfold nClass
  rw [hI, hsplit, hIoi, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

/-- Smoothing at `E`: `∫ η/(|x − E| + η) dϱ ≤ 4η(L + 1) C_m + 2^{−L}` when `|m| ≤ C_m` on
`E + i[η, 1]` and `2^L η ≤ 1`. -/
private lemma qc_smooth (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E η Cm : ℝ}
    (L : ℕ) (hη : 0 < η) (hL : 2 ^ L * η ≤ 1)
    (hm : ∀ y ∈ Set.Icc η 1, ‖mFun K σ (↑E + ↑y * Complex.I)‖ ≤ Cm) :
    ∫ x, η / (|x - E| + η) ∂(varrho K σ) ≤ 4 * η * (L + 1) * Cm + 1 / 2 ^ L := by
  have h := smooth_int_le σ hσ hK E η hη L
  have hl : ∀ l ∈ Finset.range (L + 1), (mFun K σ (↑E + ↑(2 ^ l * η) * Complex.I)).im ≤ Cm := by
    intro l hl
    have hlL : l ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have h2l : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
    have h2lL : (2 : ℝ) ^ l ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hlL
    have hyl : 2 ^ l * η ∈ Set.Icc η 1 := ⟨by nlinarith, by nlinarith⟩
    exact (Complex.im_le_norm _).trans (hm _ hyl)
  have hsum := Finset.sum_le_sum hl
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  calc ∫ x, η / (|x - E| + η) ∂(varrho K σ)
      ≤ 4 * η * ∑ l ∈ Finset.range (L + 1), (mFun K σ (↑E + ↑(2 ^ l * η) * Complex.I)).im +
          1 / 2 ^ L := h
    _ ≤ 4 * η * ((L + 1) * Cm) + 1 / 2 ^ L := by
        have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 * η)
        linarith
    _ = 4 * η * (L + 1) * Cm + 1 / 2 ^ L := by ring

/-- The smoothed count `K ϱ([E₁, E₂])` against `(K/π) ∫ Im m(x + iη) dx`. -/
private lemma qc_count_one (K : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK : 0 < K) {E₁ E₂ η : ℝ}
    (hη : 0 < η) (h12 : E₁ ≤ E₂) (hE₂ : 0 < E₂) :
    |(nClass K σ E₁ - nClass K σ E₂) -
        K * (∫ x in E₁..E₂, (mFun K σ (↑x + ↑η * Complex.I)).im) / Real.pi| ≤
      2 * K * ∫ x, (η / (|x - E₁| + η) + η / (|x - E₂| + η)) ∂(varrho K σ) := by
  have hprob := isProbabilityMeasure_varrho K σ hσ hK
  have hpi := Real.pi_pos
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [qc_nClass_sub K σ hσ hK h12 hE₂, arctan_count_varrho σ hσ hK E₁ E₂ η hη]
  have hFint := qc_integrable_arcdiff (varrho K σ) E₁ E₂ η
  have hind : Integrable (fun t : ℝ => (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t)
      (varrho K σ) := (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have hg : Integrable (fun x : ℝ => η / (|x - E₁| + η) + η / (|x - E₂| + η)) (varrho K σ) :=
    (qc_integrable_decay _ E₁ η hη).add (qc_integrable_decay _ E₂ η hη)
  have hC : |(∫ t, (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) ∂(varrho K σ)) /
        Real.pi - ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho K σ)| ≤
      2 * ∫ x, (η / (|x - E₁| + η) + η / (|x - E₂| + η)) ∂(varrho K σ) := by
    rw [← integral_div, ← integral_sub (hFint.div_const _) hind, ← integral_const_mul]
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le (hg.const_mul 2)
      (ae_of_all _ fun t => ?_))
    rw [Real.norm_eq_abs]
    have := arctan_indicator_le (x := t) hη h12
    calc |(Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) / Real.pi -
          (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t|
        ≤ 2 * η / (|t - E₁| + η) + 2 * η / (|t - E₂| + η) := this
      _ = 2 * (η / (|t - E₁| + η) + η / (|t - E₂| + η)) := by ring
  have e : (K : ℝ) * ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho K σ) -
      K * (∫ t, (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) ∂(varrho K σ)) /
        Real.pi =
      -(K * ((∫ t, (Real.arctan ((E₂ - t) / η) - Real.arctan ((E₁ - t) / η)) ∂(varrho K σ)) /
        Real.pi - ∫ t, (Set.Icc E₁ E₂).indicator (fun _ => (1 : ℝ)) t ∂(varrho K σ))) := by
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg hK0]
  have := mul_le_mul_of_nonneg_left hC hK0
  linarith

/-- Two-measure comparison: with `|K₁ m_{K₁} − K₂ m_{K₂}| ≤ B/y` on `E_j + i[η, 1]` and `≤ B` on
`[E₁, E₂] + i`, and `|m_{K_i}| ≤ C_m` on the vertical segments, the counts `n_{K₁}` and `n_{K₂}`
on `[E₁, E₂]` differ by at most `B(E₂ − E₁ + 2 log(1/η)) + 4(K₁ + K₂)(4η(L+1)C_m + 2^{−L})`. -/
private lemma qc_count_two (K₁ K₂ : ℕ) (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hK₁ : 0 < K₁)
    (hK₂ : 0 < K₂) {E₁ E₂ η B Cm : ℝ} (L : ℕ) (hη : 0 < η) (hL : 2 ^ L * η ≤ 1)
    (h12 : E₁ ≤ E₂) (hE₂ : 0 < E₂)
    (hline : ∀ E, (E = E₁ ∨ E = E₂) → ∀ y ∈ Set.Icc η 1,
      ‖(K₁ : ℂ) * mFun K₁ σ (↑E + ↑y * Complex.I) - K₂ * mFun K₂ σ (↑E + ↑y * Complex.I)‖ ≤
        B / y ∧ ‖mFun K₁ σ (↑E + ↑y * Complex.I)‖ ≤ Cm ∧
        ‖mFun K₂ σ (↑E + ↑y * Complex.I)‖ ≤ Cm)
    (htop : ∀ x ∈ Set.Icc E₁ E₂,
      ‖(K₁ : ℂ) * mFun K₁ σ (↑x + ↑(1 : ℝ) * Complex.I) -
          K₂ * mFun K₂ σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ B) :
    |(nClass K₁ σ E₁ - nClass K₁ σ E₂) - (nClass K₂ σ E₁ - nClass K₂ σ E₂)| ≤
      B * (E₂ - E₁ + 2 * Real.log (1 / η)) +
        4 * (K₁ + K₂) * (4 * η * (L + 1) * Cm + 1 / 2 ^ L) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have h2L : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  have hη1 : η ≤ 1 := by nlinarith
  have hB : 0 ≤ B := by
    have := (hline E₁ (Or.inl rfl) 1 ⟨hη1, le_rfl⟩).1
    have := (norm_nonneg _).trans this
    simpa using this
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have hK₁r : (0 : ℝ) ≤ K₁ := Nat.cast_nonneg _
  have hK₂r : (0 : ℝ) ≤ K₂ := Nat.cast_nonneg _
  -- the two smoothing errors
  have hsm : ∀ K, 0 < K → (∀ E, (E = E₁ ∨ E = E₂) → ∀ y ∈ Set.Icc η 1,
      ‖mFun K σ (↑E + ↑y * Complex.I)‖ ≤ Cm) →
      ∫ x, (η / (|x - E₁| + η) + η / (|x - E₂| + η)) ∂(varrho K σ) ≤
        2 * (4 * η * (L + 1) * Cm + 1 / 2 ^ L) := by
    intro K hK hm
    have := isProbabilityMeasure_varrho K σ hσ hK
    rw [integral_add (qc_integrable_decay _ E₁ η hη) (qc_integrable_decay _ E₂ η hη)]
    have a := qc_smooth K σ hσ hK L hη hL (hm E₁ (Or.inl rfl))
    have b := qc_smooth K σ hσ hK L hη hL (hm E₂ (Or.inr rfl))
    linarith
  have s1 := hsm K₁ hK₁ fun E hE y hy => (hline E hE y hy).2.1
  have s2 := hsm K₂ hK₂ fun E hE y hy => (hline E hE y hy).2.2
  have c1 := qc_count_one K₁ σ hσ hK₁ hη h12 hE₂
  have c2 := qc_count_one K₂ σ hσ hK₂ hη h12 hE₂
  -- the contour term
  set F : ℂ → ℂ := fun z => (K₁ : ℂ) * mFun K₁ σ z - K₂ * mFun K₂ σ z with hF
  have hcF : ContinuousOn F {z : ℂ | 0 < z.im} :=
    (continuousOn_const.mul (analyticOnNhd_mFun K₁ σ hσ).continuousOn).sub
      (continuousOn_const.mul (analyticOnNhd_mFun K₂ σ hσ).continuousOn)
  have iH : ∀ (K : ℕ) (y : ℝ), 0 < y → IntervalIntegrable
      (fun x : ℝ => (mFun K σ (↑x + ↑y * Complex.I)).im) volume E₁ E₂ :=
    fun K y hy => (Complex.continuous_im.comp (qc_cont_hor K σ hσ hy)).intervalIntegrable _ _
  have iV : ∀ (K : ℕ) (E : ℝ), IntervalIntegrable
      (fun y : ℝ => (mFun K σ (↑E + ↑y * Complex.I)).re) volume η 1 :=
    fun K E => (Complex.continuous_re.comp_continuousOn
      (qc_cont_ver K σ hσ E hη hη1)).intervalIntegrable
  have seg1 := segment_identity_m σ hσ hK₁ E₁ E₂ η 1 hη hη1
  have seg2 := segment_identity_m σ hσ hK₂ E₁ E₂ η 1 hη hη1
  have hFim : ∀ y : ℝ, 0 < y → ∀ x : ℝ, (F (↑x + ↑y * Complex.I)).im =
      K₁ * (mFun K₁ σ (↑x + ↑y * Complex.I)).im - K₂ * (mFun K₂ σ (↑x + ↑y * Complex.I)).im := by
    intro y _ x
    simp [hF, Complex.sub_im, Complex.mul_im]
  have hFre : ∀ (E y : ℝ), (F (↑E + ↑y * Complex.I)).re =
      K₁ * (mFun K₁ σ (↑E + ↑y * Complex.I)).re - K₂ * (mFun K₂ σ (↑E + ↑y * Complex.I)).re := by
    intro E y
    simp [hF, Complex.sub_re, Complex.mul_re]
  have hcontour : (K₁ : ℝ) * (∫ x in E₁..E₂, (mFun K₁ σ (↑x + ↑η * Complex.I)).im) -
      K₂ * (∫ x in E₁..E₂, (mFun K₂ σ (↑x + ↑η * Complex.I)).im) =
      (∫ x in E₁..E₂, (F (↑x + ↑(1 : ℝ) * Complex.I)).im) -
        ((∫ y in η..1, (F (↑E₂ + ↑y * Complex.I)).re) -
          ∫ y in η..1, (F (↑E₁ + ↑y * Complex.I)).re) := by
    simp_rw [hFim 1 one_pos, hFre]
    rw [intervalIntegral.integral_sub ((iH K₁ 1 one_pos).const_mul _)
        ((iH K₂ 1 one_pos).const_mul _),
      intervalIntegral.integral_sub ((iV K₁ E₂).const_mul _) ((iV K₂ E₂).const_mul _),
      intervalIntegral.integral_sub ((iV K₁ E₁).const_mul _) ((iV K₂ E₁).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, seg1, seg2,
      intervalIntegral.integral_sub (iV K₁ E₂) (iV K₁ E₁),
      intervalIntegral.integral_sub (iV K₂ E₂) (iV K₂ E₁)]
    ring
  have hb1 : |∫ x in E₁..E₂, (F (↑x + ↑(1 : ℝ) * Complex.I)).im| ≤ B * (E₂ - E₁) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂) (C := B)
      (f := fun x : ℝ => (F (↑x + ↑(1 : ℝ) * Complex.I)).im) (fun x hx => by
        rw [Set.uIoc_of_le h12] at hx
        exact (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm _).trans (htop x ⟨hx.1.le, hx.2⟩))
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 h12)] at this
  have hb2 : ∀ E, (E = E₁ ∨ E = E₂) →
      |∫ y in η..1, (F (↑E + ↑y * Complex.I)).re| ≤ B * Real.log (1 / η) := by
    intro E hE
    have hg : IntervalIntegrable (fun y : ℝ => B * y⁻¹) volume η 1 := by
      refine (continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => ?_)).intervalIntegrable
      rw [Set.uIcc_of_le hη1] at hy
      exact (lt_of_lt_of_le hη hy.1).ne'
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun y : ℝ => (F (↑E + ↑y * Complex.I)).re) hη1 (ae_of_all _ fun y hy => by
      refine (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans ?_
      refine ((hline E hE y ⟨hy.1.le, hy.2⟩).1).trans (le_of_eq ?_)
      field_simp) hg
    rwa [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hη one_pos] at this
  have hT : |(K₁ : ℝ) * (∫ x in E₁..E₂, (mFun K₁ σ (↑x + ↑η * Complex.I)).im) -
      K₂ * (∫ x in E₁..E₂, (mFun K₂ σ (↑x + ↑η * Complex.I)).im)| ≤
      B * (E₂ - E₁ + 2 * Real.log (1 / η)) := by
    rw [hcontour]
    have h1 := hb2 E₁ (Or.inl rfl)
    have h2 := hb2 E₂ (Or.inr rfl)
    have := abs_sub (∫ x in E₁..E₂, (F (↑x + ↑(1 : ℝ) * Complex.I)).im)
      ((∫ y in η..1, (F (↑E₂ + ↑y * Complex.I)).re) - ∫ y in η..1, (F (↑E₁ + ↑y * Complex.I)).re)
    have := abs_sub (∫ y in η..1, (F (↑E₂ + ↑y * Complex.I)).re)
      (∫ y in η..1, (F (↑E₁ + ↑y * Complex.I)).re)
    nlinarith
  -- assembly
  set I₁ := ∫ x in E₁..E₂, (mFun K₁ σ (↑x + ↑η * Complex.I)).im
  set I₂ := ∫ x in E₁..E₂, (mFun K₂ σ (↑x + ↑η * Complex.I)).im
  have e : (nClass K₁ σ E₁ - nClass K₁ σ E₂) - (nClass K₂ σ E₁ - nClass K₂ σ E₂) =
      ((nClass K₁ σ E₁ - nClass K₁ σ E₂) - K₁ * I₁ / Real.pi) -
        ((nClass K₂ σ E₁ - nClass K₂ σ E₂) - K₂ * I₂ / Real.pi) +
        (K₁ * I₁ - K₂ * I₂) / Real.pi := by
    field_simp
    ring
  rw [e]
  have hT' : |(K₁ * I₁ - K₂ * I₂) / Real.pi| ≤ B * (E₂ - E₁ + 2 * Real.log (1 / η)) := by
    rw [abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have : 0 ≤ B * (E₂ - E₁ + 2 * Real.log (1 / η)) := by
      have : 0 ≤ E₂ - E₁ := sub_nonneg.2 h12
      positivity
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left s1 (by positivity : (0 : ℝ) ≤ 2 * K₁)
  have hm2 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ 2 * K₂)
  calc _ ≤ |(nClass K₁ σ E₁ - nClass K₁ σ E₂) - K₁ * I₁ / Real.pi| +
        |(nClass K₂ σ E₁ - nClass K₂ σ E₂) - K₂ * I₂ / Real.pi| +
        |(K₁ * I₁ - K₂ * I₂) / Real.pi| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by nlinarith

/-- `|n_{N−1}(E) − n_N(E)| ≤ N^δ` for `E ≥ τ` (no regularity). -/
theorem nClass_pred_sub (τ δ : ℝ) (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), DensityAssumptions τ N σ →
      ∀ E : ℝ, τ ≤ E → |nClass (N - 1) σ E - nClass N σ E| ≤ (N : ℝ) ^ δ := by
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  set Emax := 4 * τ⁻¹ * (1 + 2 * τ⁻¹) with hEmax
  have hEmax0 : 0 < Emax := by positivity
  set E₂ := Emax + 1 with hE₂
  set τ' := min (τ / 2) (E₂ + 1)⁻¹ with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτ'τ : τ' ≤ τ / 2 := min_le_left _ _
  have hτ'E : E₂ + 1 ≤ τ'⁻¹ := le_inv_of_le_inv₀ (by positivity) (min_le_right _ _)
  set Cm := genPropConst τ' with hCm
  have hCm0 : 0 < Cm := by rw [hCm, genPropConst]; positivity
  obtain ⟨C₀, N₁, hsub⟩ := mFun_pred_sub τ' hτ'0
  set B := |C₀| + Cm with hB
  have hB0 : 0 ≤ B := by positivity
  set K₀ := B * E₂ + 32 * Cm + 16 with hK₀
  set K₁ := 2 * B + 64 * Cm with hK₁
  set A := max 1 (K₀ + K₁ * (2 / δ)) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨⌈(N₁ : ℝ) + A ^ (2 / δ) + 2⌉₊, ?_⟩
  intro N hN M σ h E hE
  have hNc : (N₁ : ℝ) + A ^ (2 / δ) + 2 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hApow : 0 ≤ A ^ (2 / δ) := Real.rpow_nonneg (by linarith) _
  have hNr : (2 : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
    linarith
  have hN2 : 2 ≤ N := by exact_mod_cast hNr
  have hNN₁ : N₁ ≤ N := by
    have : (N₁ : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hK : 0 < N := by omega
  have hK1 : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by linarith
  have hσ := h.nonneg
  have h1 := qc_da_pred h hN2
  have hτ1 : τ ≤ 1 := by
    have h' : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    push Not at hc
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
    linarith
  have hNδ : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hN0.le _
  have hbd1 : 2 * τ⁻¹ * (1 + τ⁻¹) ≤ Emax := by rw [hEmax]; nlinarith
  have hbd2 : 2 * (τ / 2)⁻¹ * (1 + (τ / 2)⁻¹) = Emax := by rw [hEmax]; field_simp; ring
  -- above the supports both counts vanish
  by_cases hbig : Emax < E
  · rw [qc_nClass_zero_above h hK (by linarith), qc_nClass_zero_above h1 hK1 (by linarith),
      sub_zero, abs_zero]
    exact hNδ
  push Not at hbig
  have hz0N : nClass N σ E₂ = 0 := qc_nClass_zero_above h hK (by linarith)
  have hz0N1 : nClass (N - 1) σ E₂ = 0 := qc_nClass_zero_above h1 hK1 (by linarith)
  have hhN := h.mono hτ'0 (by linarith)
  have hhN1 := h1.mono hτ'0 hτ'τ
  have hcast : ((N - 1 : ℕ) : ℂ) = (N : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- the bounds on the segments
  have hpt : ∀ x y : ℝ, τ ≤ x → x ≤ E₂ → 0 < y → y ≤ 1 →
      ‖(((N - 1 : ℕ) : ℂ)) * mFun (N - 1) σ (↑x + ↑y * Complex.I) -
          (N : ℂ) * mFun N σ (↑x + ↑y * Complex.I)‖ ≤ (|C₀| + Cm * y) / y ∧
        ‖mFun (N - 1) σ (↑x + ↑y * Complex.I)‖ ≤ Cm ∧
        ‖mFun N σ (↑x + ↑y * Complex.I)‖ ≤ Cm := by
    intro x y hx1 hx2 hy0 hy1
    have hzi : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by rw [qc_path_im]; exact hy0
    have hz1 : τ' ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + (y : ℂ) * Complex.I)
      rw [qc_path_re, abs_of_pos (by linarith)] at this
      linarith
    have hz2 : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ τ'⁻¹ := by
      calc ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |x| + |y| := by simp
        _ ≤ E₂ + 1 := by rw [abs_of_pos (by linarith), abs_of_pos hy0]; linarith
        _ ≤ τ'⁻¹ := hτ'E
    obtain ⟨-, hm1, -⟩ := gen_prop_m hhN1 hzi hz1 hz2
    obtain ⟨-, hm2, -⟩ := gen_prop_m hhN hzi hz1 hz2
    have hs := hsub N hNN₁ M σ hhN _ hzi hz1 hz2
    rw [qc_path_im] at hs
    refine ⟨?_, hm1, hm2⟩
    rw [hcast]
    have e : ((N : ℂ) - 1) * mFun (N - 1) σ (↑x + ↑y * Complex.I) -
        (N : ℂ) * mFun N σ (↑x + ↑y * Complex.I) =
        (N : ℂ) * (mFun (N - 1) σ (↑x + ↑y * Complex.I) - mFun N σ (↑x + ↑y * Complex.I)) -
          mFun (N - 1) σ (↑x + ↑y * Complex.I) := by ring
    rw [e]
    calc _ ≤ ‖(N : ℂ) * (mFun (N - 1) σ (↑x + ↑y * Complex.I) -
          mFun N σ (↑x + ↑y * Complex.I))‖ + ‖mFun (N - 1) σ (↑x + ↑y * Complex.I)‖ :=
          norm_sub_le _ _
      _ ≤ N * (C₀ / (N * y)) + Cm := by
          rw [norm_mul, Complex.norm_natCast]
          gcongr
      _ ≤ (|C₀| + Cm * y) / y := by
          have : (N : ℝ) * (C₀ / (N * y)) = C₀ / y := by field_simp
          rw [this, add_div, mul_div_assoc, div_self hy0.ne', mul_one]
          have : C₀ / y ≤ |C₀| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
          linarith
  -- the parameters `η = 1/N`, `L = ⌊log₂ N⌋`
  set η := 1 / (N : ℝ) with hη
  have hη0 : 0 < η := by positivity
  set L := Nat.log 2 N with hL
  have h2L : (2 : ℝ) ^ L ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have h2L' : (N : ℝ) < 2 * 2 ^ L := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    rw [pow_succ] at this
    have : (N : ℝ) < ((2 ^ L * 2 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hLη : 2 ^ L * η ≤ 1 := by
    rw [hη, mul_one_div, div_le_one hN0]; exact h2L
  have hline : ∀ E', (E' = E ∨ E' = E₂) → ∀ y ∈ Set.Icc η 1,
      ‖(((N - 1 : ℕ) : ℂ)) * mFun (N - 1) σ (↑E' + ↑y * Complex.I) -
          (N : ℂ) * mFun N σ (↑E' + ↑y * Complex.I)‖ ≤ B / y ∧
        ‖mFun (N - 1) σ (↑E' + ↑y * Complex.I)‖ ≤ Cm ∧
        ‖mFun N σ (↑E' + ↑y * Complex.I)‖ ≤ Cm := by
    intro E' hE' y hy
    have hy0 : 0 < y := lt_of_lt_of_le hη0 hy.1
    have hx1 : τ ≤ E' := by rcases hE' with rfl | rfl <;> linarith
    have hx2 : E' ≤ E₂ := by rcases hE' with rfl | rfl <;> linarith
    obtain ⟨a, b, c⟩ := hpt E' y hx1 hx2 hy0 hy.2
    refine ⟨a.trans ?_, b, c⟩
    refine div_le_div_of_nonneg_right ?_ hy0.le
    have : Cm * y ≤ Cm := by nlinarith [hy.2]
    linarith
  have htop : ∀ x ∈ Set.Icc E E₂,
      ‖(((N - 1 : ℕ) : ℂ)) * mFun (N - 1) σ (↑x + ↑(1 : ℝ) * Complex.I) -
          (N : ℂ) * mFun N σ (↑x + ↑(1 : ℝ) * Complex.I)‖ ≤ B := by
    intro x hx
    obtain ⟨a, -, -⟩ := hpt x 1 (by linarith [hx.1]) hx.2 one_pos le_rfl
    simpa [hB] using a
  have hmain := qc_count_two (N - 1) N σ hσ hK1 hK L hη0 hLη (by linarith) (by positivity)
    hline htop
  rw [hz0N, hz0N1, sub_zero, sub_zero] at hmain
  -- the numerics
  have hlogN : Real.log (1 / η) = Real.log N := by rw [hη, one_div_one_div]
  rw [hlogN] at hmain
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hLlog : (L : ℝ) ≤ 2 * Real.log N := by
    have h3 : (L : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2L
    have h4 := Real.log_two_gt_d9
    have h5 : (L : ℝ) * (1 / 2) ≤ (L : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by norm_num at h4 ⊢; linarith) (Nat.cast_nonneg _)
    linarith
  have hcast1 : ((N - 1 : ℕ) : ℝ) + N ≤ 2 * N := by
    rw [qc_cast_pred hN2]; linarith
  have hsmall : 4 * η * (L + 1) * Cm + 1 / 2 ^ L ≤ (4 * (L + 1) * Cm + 2) / N := by
    rw [hη]
    have : 1 / (2 : ℝ) ^ L ≤ 2 / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]; linarith
    have e : 4 * (1 / (N : ℝ)) * (L + 1) * Cm = 4 * (L + 1) * Cm / N := by ring
    rw [e, add_div]
    linarith
  have hsm2 : 4 * (((N - 1 : ℕ) : ℝ) + N) * (4 * η * (L + 1) * Cm + 1 / 2 ^ L) ≤
      8 * (4 * (L + 1) * Cm + 2) := by
    have hs0 : 0 ≤ 4 * η * (L + 1) * Cm + 1 / 2 ^ L := by positivity
    calc 4 * (((N - 1 : ℕ) : ℝ) + N) * (4 * η * (L + 1) * Cm + 1 / 2 ^ L)
        ≤ 4 * (2 * N) * ((4 * (L + 1) * Cm + 2) / N) := by
          gcongr
      _ = 8 * (4 * (L + 1) * Cm + 2) := by field_simp; norm_num
  have hbound : |nClass (N - 1) σ E - nClass N σ E| ≤ K₀ + K₁ * Real.log N := by
    refine hmain.trans ?_
    have h5 : B * (E₂ - E + 2 * Real.log N) ≤ B * E₂ + 2 * B * Real.log N := by
      have : 0 ≤ B * E := mul_nonneg hB0 (by linarith)
      have e : B * (E₂ - E + 2 * Real.log N) = B * E₂ + 2 * B * Real.log N - B * E := by ring
      rw [e]; linarith
    have h6 : 8 * (4 * (L + 1) * Cm + 2) ≤ 32 * Cm + 16 + 64 * Cm * Real.log N := by
      have h7 := mul_le_mul_of_nonneg_left hLlog (by positivity : (0 : ℝ) ≤ 32 * Cm)
      have e : 8 * (4 * (L + 1) * Cm + 2) = 32 * Cm * L + 32 * Cm + 16 := by ring
      rw [e]; linarith
    rw [hK₀, hK₁]
    linarith
  -- `K₀ + K₁ log N ≤ N^δ`
  have hlogd : Real.log N ≤ (N : ℝ) ^ (δ / 2) / (δ / 2) :=
    Real.log_le_rpow_div hN0.le (by positivity)
  have hP : A ≤ (N : ℝ) ^ (δ / 2) := by
    have h7 : A ^ (2 / δ) ≤ N := by linarith
    have h8 : (A ^ (2 / δ)) ^ (δ / 2) ≤ (N : ℝ) ^ (δ / 2) :=
      Real.rpow_le_rpow hApow h7 (by positivity)
    rwa [← Real.rpow_mul (by linarith), show 2 / δ * (δ / 2) = 1 by field_simp,
      Real.rpow_one] at h8
  have hNδ' : (N : ℝ) ^ δ = (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hK₁0 : 0 ≤ K₁ := by positivity
  set P := (N : ℝ) ^ (δ / 2) with hPdef
  have hP1 : 1 ≤ P := hA1.trans hP
  calc |nClass (N - 1) σ E - nClass N σ E| ≤ K₀ + K₁ * Real.log N := hbound
    _ ≤ K₀ + K₁ * (P / (δ / 2)) := by gcongr
    _ ≤ (K₀ + K₁ * (2 / δ)) * P := by
        have e : K₁ * (P / (δ / 2)) = K₁ * (2 / δ) * P := by field_simp
        rw [e]
        have h9 := mul_le_mul_of_nonneg_left hP1 hK₀0
        have e2 : (K₀ + K₁ * (2 / δ)) * P = K₀ * P + K₁ * (2 / δ) * P := by ring
        rw [e2]; linarith
    _ ≤ A * P := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    _ ≤ P * P := mul_le_mul_of_nonneg_right hP (by linarith)
    _ = (N : ℝ) ^ δ := hNδ'.symm

#print axioms mFun_pred_sub
#print axioms nClass_pred_sub
#print axioms nClass_pred_gap
#print axioms edge_pred
#print axioms edge_pred_D6

end Anisotropic
