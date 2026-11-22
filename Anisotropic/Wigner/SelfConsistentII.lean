module

public import Anisotropic.MainDefs
public import Anisotropic.Density.SelfConsistent
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.SelfConsistent

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # `m^W`: existence by continuation, its equation, derivative, lower bound on `Im m^W`, and `Ψ^W` -/

/-! ## Auxiliary facts on `m_A`, `S(w) = N⁻¹ ∑ᵢ |aᵢ − w|⁻²` and `T(w) = N⁻¹ ∑ᵢ (aᵢ − w)⁻²` -/

/-- `S(w) = N⁻¹ ∑ᵢ |aᵢ − w|⁻²`. -/
private def scW_S {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹

/-- `T(w) = N⁻¹ ∑ᵢ (aᵢ − w)⁻²`, the derivative of `m_A`. -/
private def scW_T {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i, (((a i : ℂ) - w) ^ 2)⁻¹

private lemma scW_isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const Complex.continuous_im

/-- For `Im w > 0`, every `aᵢ − w` is nonzero. -/
private lemma scW_normSq_pos {N : ℕ} (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im)
    (i : Fin N) : 0 < Complex.normSq ((a i : ℂ) - w) := by
  apply Complex.normSq_pos.2
  intro h0
  have := congrArg Complex.im h0
  simp at this
  linarith

private lemma scW_ne_zero {N : ℕ} (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im) (i : Fin N) :
    (a i : ℂ) - w ≠ 0 :=
  Complex.normSq_pos.1 (scW_normSq_pos a hw i)

/-- `‖x⁻¹‖² = |x|⁻²`. -/
private lemma scW_norm_inv_sq (x : ℂ) : ‖x⁻¹‖ ^ 2 = (Complex.normSq x)⁻¹ := by
  rw [norm_inv, inv_pow, Complex.sq_norm]

private lemma scW_S_nonneg {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : 0 ≤ scW_S a w := by
  unfold scW_S
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => inv_nonneg.2 (Complex.normSq_nonneg _))

private lemma scW_S_pos {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im) :
    0 < scW_S a w := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold scW_S
  refine mul_pos (inv_pos.2 hNpos)
    (Finset.sum_pos (fun i _ => inv_pos.2 (scW_normSq_pos a hw i)) ?_)
  exact ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-- If `c ≤ |aᵢ − w|²` for all `i`, then `S(w) ≤ c⁻¹`. -/
private lemma scW_S_le {N : ℕ} (a : Fin N → ℝ) {w : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ i, c ≤ Complex.normSq ((a i : ℂ) - w)) : scW_S a w ≤ c⁻¹ := by
  unfold scW_S
  have hs : ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ ≤ ∑ _i : Fin N, c⁻¹ :=
    Finset.sum_le_sum fun i _ => inv_anti₀ hc (h i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, _root_.inv_zero, zero_mul]
    exact inv_nonneg.2 hc.le
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
    calc (N : ℝ)⁻¹ * ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ ≤ (N : ℝ)⁻¹ * (N * c⁻¹) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = c⁻¹ := by field_simp

/-- If `|aᵢ − w|² ≤ c` for all `i` and `N ≥ 1`, then `c⁻¹ ≤ S(w)`. -/
private lemma scW_S_ge {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im) {c : ℝ}
    (h : ∀ i, Complex.normSq ((a i : ℂ) - w) ≤ c) : c⁻¹ ≤ scW_S a w := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold scW_S
  have hs : ∑ _i : Fin N, c⁻¹ ≤ ∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ :=
    Finset.sum_le_sum fun i _ => inv_anti₀ (scW_normSq_pos a hw i) (h i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc c⁻¹ = (N : ℝ)⁻¹ * (N * c⁻¹) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- `Im m_A(w) = Im w · S(w)`. -/
private lemma scW_im_stieltjesA {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    (stieltjesA a w).im = w.im * scW_S a w := by
  unfold stieltjesA scW_S
  rw [show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
    Complex.im_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-- `‖m_A(w)‖ ≤ (S(w) + 1)/2` for `N ≥ 1`. -/
private lemma scW_norm_stieltjesA_le {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) (w : ℂ) :
    ‖stieltjesA a w‖ ≤ (scW_S a w + 1) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ‖stieltjesA a w‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖ := by
    unfold stieltjesA
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have hle : ∑ i, ‖((a i : ℂ) - w)⁻¹‖ ≤
      ∑ i, ((Complex.normSq ((a i : ℂ) - w))⁻¹ + 1) / 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← scW_norm_inv_sq]
    nlinarith [sq_nonneg (‖((a i : ℂ) - w)⁻¹‖ - 1)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hle
  calc ‖stieltjesA a w‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖((a i : ℂ) - w)⁻¹‖ := h1
    _ ≤ (N : ℝ)⁻¹ * ((∑ i, (Complex.normSq ((a i : ℂ) - w))⁻¹ + N) / 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (scW_S a w + 1) / 2 := by unfold scW_S; field_simp

/-- `‖T(w)‖ ≤ S(w)`. -/
private lemma scW_norm_T_le {N : ℕ} (a : Fin N → ℝ) (w : ℂ) : ‖scW_T a w‖ ≤ scW_S a w := by
  unfold scW_T scW_S
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
    (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))) (by positivity)
  rw [norm_inv, norm_pow, Complex.sq_norm]

/-- `Im(w − m_A(w)) = Im w · (1 − S(w))`; hence `S(w) < 1` when `Im w > 0` and
`Im(w − m_A(w)) > 0`. -/
private lemma scW_S_lt_one {N : ℕ} (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im)
    (hg : 0 < (w - stieltjesA a w).im) : scW_S a w < 1 := by
  rw [Complex.sub_im, scW_im_stieltjesA] at hg
  by_contra h
  push Not at h
  nlinarith

/-- `w ↦ w − m_A(w)` has strict derivative `1 − T(w)` on `ℂ₊`. -/
private lemma scW_hasStrictDerivAt {N : ℕ} (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasStrictDerivAt (fun x => x - stieltjesA a x) (1 - scW_T a w) w := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasStrictDerivAt (fun y => ((a i : ℂ) - y)⁻¹) ((((a i : ℂ) - w) ^ 2)⁻¹) w := by
    intro i _
    have h1 := (hasStrictDerivAt_inv (scW_ne_zero a hw i)).comp w
      ((hasStrictDerivAt_id w).const_sub (a i : ℂ))
    convert h1 using 1
    · rfl
    · ring
  have hs := (HasStrictDerivAt.sum h).const_mul ((N : ℂ)⁻¹)
  have hA : HasStrictDerivAt (stieltjesA a) (scW_T a w) w := by
    unfold stieltjesA scW_T
    convert hs using 1
    funext y
    simp [Finset.sum_apply]
  exact (hasStrictDerivAt_id w).sub hA

/-- `1 − T(w) ≠ 0` when `Im w > 0` and `Im(w − m_A(w)) > 0`. -/
private lemma scW_one_sub_T_ne {N : ℕ} (a : Fin N → ℝ) {w : ℂ} (hw : 0 < w.im)
    (hg : 0 < (w - stieltjesA a w).im) : 1 - scW_T a w ≠ 0 := by
  intro h0
  have h1 : scW_T a w = 1 := (sub_eq_zero.1 h0).symm
  have h2 := scW_norm_T_le a w
  rw [h1, norm_one] at h2
  linarith [scW_S_lt_one a hw hg]

/-- A preimage `w ∈ ℂ₊` of `z` under `w ↦ w − m_A(w)` gives the solution `m = w − z`. -/
private lemma scW_sol_of_preimage {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ}
    (hw : 0 < w.im) : 0 < (stieltjesA a w).im ∧
      stieltjesA a w = stieltjesA a ((w - stieltjesA a w) + stieltjesA a w) := by
  refine ⟨?_, by rw [sub_add_cancel]⟩
  rw [scW_im_stieltjesA]
  exact mul_pos hw (scW_S_pos hN a hw)

/-- At a solution `m` of `m = m_A(z + m)` with `Im m > 0` and `Im z > 0`, `S(z + m) < 1`. -/
private lemma scW_S_lt_one_of_sol {N : ℕ} (a : Fin N → ℝ) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im) (heq : m = stieltjesA a (z + m)) : scW_S a (z + m) < 1 := by
  have hw : 0 < (z + m).im := by simp; linarith
  refine scW_S_lt_one a hw ?_
  rw [← heq]
  simpa using hz

/-- Uniqueness of the solution of `m = m_A(z + m)` in `ℂ₊` for `Im z > 0` (§12.1). -/
private lemma scW_unique {N : ℕ} (a : Fin N → ℝ) {z m₁ m₂ : ℂ} (hz : 0 < z.im)
    (hm₁ : 0 < m₁.im) (heq₁ : m₁ = stieltjesA a (z + m₁))
    (hm₂ : 0 < m₂.im) (heq₂ : m₂ = stieltjesA a (z + m₂)) : m₁ = m₂ := by
  have hw₁ : 0 < (z + m₁).im := by simp; linarith
  have hw₂ : 0 < (z + m₂).im := by simp; linarith
  set d₁ : Fin N → ℂ := fun i => (a i : ℂ) - (z + m₁)
  set d₂ : Fin N → ℂ := fun i => (a i : ℂ) - (z + m₂)
  have hd₁ : ∀ i, d₁ i ≠ 0 := fun i => scW_ne_zero a hw₁ i
  have hd₂ : ∀ i, d₂ i ≠ 0 := fun i => scW_ne_zero a hw₂ i
  set F : ℂ := (N : ℂ)⁻¹ * ∑ i, (d₁ i * d₂ i)⁻¹
  have hdiff : m₁ - m₂ = (m₁ - m₂) * F := by
    conv_lhs => rw [heq₁, heq₂]
    unfold stieltjesA
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp only [F]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hd₁ i
    have h2 := hd₂ i
    simp only [d₁, d₂] at h1 h2 ⊢
    field_simp
    ring
  have hF : ‖F‖ < 1 := by
    have hS₁ := scW_S_lt_one_of_sol a hz hm₁ heq₁
    have hS₂ := scW_S_lt_one_of_sol a hz hm₂ heq₂
    unfold scW_S at hS₁ hS₂
    have hle : ‖F‖ ≤ (N : ℝ)⁻¹ * ∑ i,
        ((Complex.normSq (d₁ i))⁻¹ + (Complex.normSq (d₂ i))⁻¹) / 2 := by
      simp only [F]
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ => ?_)) (by positivity)
      rw [mul_inv, norm_mul, ← scW_norm_inv_sq, ← scW_norm_inv_sq]
      nlinarith [sq_nonneg (‖(d₁ i)⁻¹‖ - ‖(d₂ i)⁻¹‖)]
    rw [← Finset.sum_div, Finset.sum_add_distrib, mul_div_assoc', mul_add] at hle
    simp only [d₁, d₂] at hle
    linarith
  by_contra hne
  have hne' : ‖m₁ - m₂‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hne)
  have h := congrArg norm hdiff
  rw [norm_mul] at h
  have hpos : 0 < ‖m₁ - m₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne')
  nlinarith

/-- Every `z ∈ ℂ₊` has a preimage `w ∈ ℂ₊` under `w ↦ w − m_A(w)`: the set of attained values
in `ℂ₊` is nonempty, open and relatively closed in the connected set `ℂ₊`. -/
private lemma scW_exists {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, 0 < w.im ∧ w - stieltjesA a w = z := by
  set g : ℂ → ℂ := fun x => x - stieltjesA a x with hg
  set U : Set ℂ := {ζ | 0 < ζ.im ∧ ∃ w : ℂ, 0 < w.im ∧ g w = ζ} with hU
  have hpre : IsPreconnected upperHalf := (convex_halfSpace_im_gt 0).isPreconnected
  -- `U` is open: inverse function theorem at a preimage.
  have hopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro ζ ⟨hζ, w, hw, rfl⟩
    have hstrict := scW_hasStrictDerivAt a hw
    have hne : 1 - scW_T a w ≠ 0 := scW_one_sub_T_ne a hw hζ
    have h1 : g '' upperHalf ∈ 𝓝 (g w) := by
      rw [← hstrict.map_nhds_eq hne]
      exact image_mem_map (scW_isOpen_upperHalf.mem_nhds hw)
    have h2 : upperHalf ∈ 𝓝 (g w) := scW_isOpen_upperHalf.mem_nhds hζ
    filter_upwards [h1, h2] with ξ hξ1 hξ2
    obtain ⟨v, hv, rfl⟩ := hξ1
    exact ⟨hξ2, v, hv, rfl⟩
  -- `U` is nonempty: the value at `w₀ = 2i`, where `S(w₀) ≤ 1/4`.
  have hne : (upperHalf ∩ U).Nonempty := by
    set w₀ : ℂ := 2 * Complex.I with hw₀
    have hw₀im : w₀.im = 2 := by simp [hw₀]
    have hS : scW_S a w₀ ≤ 4⁻¹ := by
      refine scW_S_le a (by norm_num) fun i => ?_
      rw [Complex.normSq_apply]
      simp only [hw₀, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
        Complex.I_re, Complex.im_ofNat, Complex.I_im, Complex.sub_im, Complex.ofReal_im,
        Complex.mul_im]
      nlinarith [sq_nonneg (a i)]
    have hpos : 0 < (g w₀).im := by
      simp only [hg]
      rw [Complex.sub_im, scW_im_stieltjesA, hw₀im]
      nlinarith
    exact ⟨g w₀, hpos, hpos, w₀, by rw [hw₀im]; norm_num, rfl⟩
  -- `U` is relatively closed in `ℂ₊`: preimages of points near `z` lie in a compact subset.
  have hclosed : closure U ∩ upperHalf ⊆ U := by
    rintro ζ₀ ⟨hzc, hz₀⟩
    change 0 < ζ₀.im at hz₀
    set K : Set ℂ := {w | ‖w‖ ≤ ‖ζ₀‖ + ζ₀.im / 2 + 1 ∧ ζ₀.im / 2 ≤ w.im} with hK
    have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im))
      ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := ‖ζ₀‖ + ζ₀.im / 2 + 1)).subset
        fun w hw => mem_closedBall_zero_iff.mpr hw.1)
    have hKpos : ∀ w ∈ K, 0 < w.im := fun w hw => lt_of_lt_of_le (by positivity) hw.2
    have hcont : ContinuousOn g K := continuousOn_of_forall_continuousAt fun w hw =>
      (scW_hasStrictDerivAt a (hKpos w hw)).hasDerivAt.continuousAt
    have hKimg : IsClosed (g '' K) := (hKc.image_of_continuousOn hcont).isClosed
    have hsub : Metric.ball ζ₀ (ζ₀.im / 2) ∩ U ⊆ g '' K := by
      rintro ζ ⟨hball, hζ, w, hw, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hball
      have him : ζ₀.im / 2 < (g w).im := by
        have h := Complex.abs_im_le_norm (g w - ζ₀)
        rw [Complex.sub_im] at h
        have := (abs_le.mp h).1
        linarith
      have hgw : (g w).im = w.im - w.im * scW_S a w := by
        simp only [hg]
        rw [Complex.sub_im, scW_im_stieltjesA]
      have hS0 := scW_S_nonneg a w
      have hS1 : scW_S a w < 1 := scW_S_lt_one a hw hζ
      have hnormA := scW_norm_stieltjesA_le hN a w
      refine ⟨w, ⟨?_, ?_⟩, rfl⟩
      · have e : w = g w + stieltjesA a w := by simp [hg]
        have h1 : ‖g w‖ ≤ ‖ζ₀‖ + ‖g w - ζ₀‖ := by
          have := norm_add_le ζ₀ (g w - ζ₀)
          rwa [add_sub_cancel] at this
        calc ‖w‖ = ‖g w + stieltjesA a w‖ := by rw [← e]
          _ ≤ ‖g w‖ + ‖stieltjesA a w‖ := norm_add_le _ _
          _ ≤ ‖ζ₀‖ + ζ₀.im / 2 + 1 := by linarith
      · have : 0 ≤ w.im * scW_S a w := mul_nonneg hw.le hS0
        linarith
    have hzK : ζ₀ ∈ g '' K := by
      have h1 : ζ₀ ∈ closure (Metric.ball ζ₀ (ζ₀.im / 2) ∩ U) :=
        Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self (by positivity), hzc⟩
      exact closure_minimal hsub hKimg h1
    obtain ⟨w, hwK, hwz⟩ := hzK
    exact ⟨hz₀, w, hKpos w hwK, hwz⟩
  exact (hpre.subset_of_closure_inter_subset hopen hne hclosed (show z ∈ upperHalf from hz)).2

/-- Existence and uniqueness of `m^W` (§12.1; proof: `w = z + m`, uniqueness from
`N⁻¹ ∑ |aᵢ − w|⁻² = Im m/(Im m + η) < 1`, existence by contraction for `η > 1` and continuation). -/
theorem existsUnique_mW {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    ∃! m : ℂ, 0 < m.im ∧ m = stieltjesA a (z + m) := by
  obtain ⟨w, hw, hgw⟩ := scW_exists hN a hz
  obtain ⟨hpos, heq⟩ := scW_sol_of_preimage hN a hw
  rw [hgw] at heq
  exact ⟨stieltjesA a w, ⟨hpos, heq⟩, fun y hy => scW_unique a hz hy.1 hy.2 hpos heq⟩

theorem mW_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < (mW a z).im ∧ mW a z = stieltjesA a (z + mW a z) := by
  have h : ∃ m : ℂ, 0 < m.im ∧ m = stieltjesA a (z + m) :=
    (existsUnique_mW hN a hz).exists
  rw [mW, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem mW_eq_of_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z m : ℂ} (hz : 0 < z.im)
    (hm : 0 < m.im) (h : m = stieltjesA a (z + m)) : mW a z = m :=
  (existsUnique_mW hN a hz).unique (mW_spec hN a hz) ⟨hm, h⟩

/-- `Im m^W ≥ (3τ⁻¹ + 1)⁻² η` for `|E| ≤ τ⁻¹`, `η ≤ τ⁻¹` and `|aᵢ| ≤ τ⁻¹`. -/
theorem im_mW_ge {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {a : Fin N → ℝ}
    (ha : ∀ i, |a i| ≤ τ⁻¹) {z : ℂ} (hz : 0 < z.im) (hE : |z.re| ≤ τ⁻¹) (hη : z.im ≤ τ⁻¹) :
    ((3 * τ⁻¹ + 1) ^ 2)⁻¹ * z.im ≤ (mW a z).im := by
  obtain ⟨hm, heq⟩ := mW_spec hN a hz
  have hmn := norm_mW_lt_one hN a hz
  have hw : 0 < (z + mW a z).im := by simp; linarith
  have hzn : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hz] at hzn
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hb : ∀ i, Complex.normSq ((a i : ℂ) - (z + mW a z)) ≤ (3 * τ⁻¹ + 1) ^ 2 := by
    intro i
    rw [← Complex.sq_norm]
    have h1 : ‖(a i : ℂ) - (z + mW a z)‖ ≤ |a i| + ‖z‖ + ‖mW a z‖ := by
      calc ‖(a i : ℂ) - (z + mW a z)‖ ≤ ‖(a i : ℂ)‖ + ‖z + mW a z‖ := norm_sub_le _ _
        _ ≤ ‖(a i : ℂ)‖ + (‖z‖ + ‖mW a z‖) := by gcongr; exact norm_add_le _ _
        _ = |a i| + ‖z‖ + ‖mW a z‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; ring
    have h2 : ‖(a i : ℂ) - (z + mW a z)‖ ≤ 3 * τ⁻¹ + 1 := by linarith [ha i]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hS := scW_S_ge hN a hw hb
  have him := congrArg Complex.im heq
  rw [scW_im_stieltjesA, Complex.add_im] at him
  have hc : 0 ≤ ((3 * τ⁻¹ + 1) ^ 2)⁻¹ := by positivity
  rw [him]
  calc ((3 * τ⁻¹ + 1) ^ 2)⁻¹ * z.im ≤ scW_S a (z + mW a z) * z.im :=
        mul_le_mul_of_nonneg_right hS hz.le
    _ ≤ scW_S a (z + mW a z) * (z.im + (mW a z).im) :=
        mul_le_mul_of_nonneg_left (by linarith) (scW_S_nonneg a _)
    _ = (z.im + (mW a z).im) * scW_S a (z + mW a z) := by ring

/-- `m^W` is holomorphic on `ℂ₊`, with `|m^W'| ≤ Im m^W/η` (`m' = T/(1 − T)`, `|T| ≤ S`). -/
theorem hasDerivAt_mW {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    ∃ m' : ℂ, HasDerivAt (mW a) m' z ∧ ‖m'‖ ≤ (mW a z).im / z.im := by
  obtain ⟨hm, heq⟩ := mW_spec hN a hz
  set m := mW a z with hmdef
  set w := z + m with hwdef
  have hw : 0 < w.im := by simp [w]; linarith
  have hgw : w - stieltjesA a w = z := by rw [← heq]; simp [w]
  have hgpos : 0 < (w - stieltjesA a w).im := by rw [hgw]; exact hz
  have hS := scW_S_lt_one a hw hgpos
  have hT := scW_norm_T_le a w
  have hne : 1 - scW_T a w ≠ 0 := scW_one_sub_T_ne a hw hgpos
  have hstrict := scW_hasStrictDerivAt a hw
  have hev : ∀ᶠ x in 𝓝 w, (fun ζ => ζ + mW a ζ) (x - stieltjesA a x) = x := by
    have h1 : upperHalf ∈ 𝓝 w := scW_isOpen_upperHalf.mem_nhds hw
    have h2 : (fun x => x - stieltjesA a x) ⁻¹' upperHalf ∈ 𝓝 w :=
      hstrict.hasDerivAt.continuousAt.preimage_mem_nhds (scW_isOpen_upperHalf.mem_nhds hgpos)
    filter_upwards [h1, h2] with x hx1 hx2
    have hx : 0 < x.im := hx1
    have hgx : 0 < (x - stieltjesA a x).im := hx2
    obtain ⟨hpx, hex⟩ := scW_sol_of_preimage hN a hx
    have := mW_eq_of_spec hN a hgx hpx hex
    simp only [this, sub_add_cancel]
  have h := (hstrict.to_local_left_inverse (g := fun ζ => ζ + mW a ζ) hne hev).hasDerivAt
  simp only [hgw] at h
  refine ⟨(1 - scW_T a w)⁻¹ - 1, ?_, ?_⟩
  · have h2 := h.sub (hasDerivAt_id z)
    convert h2 using 1
    funext ζ
    simp
  · have him := congrArg Complex.im heq
    rw [scW_im_stieltjesA, Complex.add_im] at him
    have hT1 : 1 - scW_S a w ≤ ‖1 - scW_T a w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (scW_T a w)
      rw [norm_one] at this
      linarith
    have hden : 0 < ‖1 - scW_T a w‖ := by linarith
    have e : (1 - scW_T a w)⁻¹ - 1 = scW_T a w / (1 - scW_T a w) := by
      field_simp
      ring
    rw [e, norm_div, div_le_div_iff₀ hden hz]
    have hS0 := scW_S_nonneg a w
    have hTn := norm_nonneg (scW_T a w)
    nlinarith [mul_le_mul_of_nonneg_left hT1 hm.le, mul_le_mul_of_nonneg_left hT hz.le]

/-- `η ↦ Ψ^W(E + iη)` is nonincreasing (§12.2, after Lemma 12.7). -/
theorem PsiW_anti {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) (E : ℝ) {y₁ y₂ : ℝ} (hy : 0 < y₁)
    (h : y₁ ≤ y₂) : PsiW a ⟨E, y₂⟩ ≤ PsiW a ⟨E, y₁⟩ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hy₂ : 0 < y₂ := lt_of_lt_of_le hy h
  set c : ℝ → ℂ := fun t => (E : ℂ) + (t : ℂ) * Complex.I with hc
  have hcim : ∀ t, (c t).im = t := fun t => by simp [hc]
  have hcpt : ∀ t, (⟨E, t⟩ : ℂ) = c t := fun t => by apply Complex.ext <;> simp [hc]
  set φ : ℝ → ℝ := fun t => (mW a (c t)).im / t with hφ
  have hderiv : ∀ t, 0 < t → ∃ d, HasDerivAt φ d t ∧ d ≤ 0 := by
    intro t ht
    have hz : 0 < (c t).im := by rw [hcim]; exact ht
    obtain ⟨m', hm', hb⟩ := hasDerivAt_mW hN a hz
    have hcd : HasDerivAt c (((1 : ℝ) : ℂ) * Complex.I) t :=
      (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).const_add (E : ℂ)
    have h1 : HasDerivAt (fun s => mW a (c s)) (m' * (((1 : ℝ) : ℂ) * Complex.I)) t :=
      hm'.comp t hcd
    have h2 : HasDerivAt (fun s => (mW a (c s)).im) (m' * (((1 : ℝ) : ℂ) * Complex.I)).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.div (hasDerivAt_id t) ht.ne'
    refine ⟨_, h3, ?_⟩
    have hre : (m' * (((1 : ℝ) : ℂ) * Complex.I)).im = m'.re := by simp
    rw [hre, hcim] at *
    have hb' : m'.re * t ≤ (mW a (c t)).im := by
      have := (Complex.re_le_norm m').trans hb
      rw [le_div_iff₀ ht] at this
      exact this
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    simp only [id]
    linarith
  have hanti : AntitoneOn φ (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro t ht
      obtain ⟨d, hd, -⟩ := hderiv t ht
      exact hd.continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      intro t ht
      obtain ⟨d, hd, -⟩ := hderiv t ht
      exact hd.differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro t ht
      obtain ⟨d, hd, hd0⟩ := hderiv t ht
      rw [hd.deriv]
      exact hd0
  have hφ12 : φ y₂ ≤ φ y₁ := hanti hy hy₂ h
  simp only [hφ] at hφ12
  unfold PsiW
  rw [hcpt, hcpt, hcim, hcim]
  have hq : (mW a (c y₂)).im / (N * y₂) ≤ (mW a (c y₁)).im / (N * y₁) := by
    rw [mul_comm (N : ℝ) y₂, mul_comm (N : ℝ) y₁, ← div_div, ← div_div]
    exact div_le_div_of_nonneg_right hφ12 hNpos.le
  have h1 : 1 / (N * y₂) ≤ 1 / (N * y₁) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left h hNpos.le)
  exact add_le_add (Real.sqrt_le_sqrt hq) h1

/-! ## Examples -/

/-- Existence and uniqueness at spectrum `(1, −1)`, `z = i`. -/
example : ∃! m : ℂ, 0 < m.im ∧ m = stieltjesA (![1, -1] : Fin 2 → ℝ) (Complex.I + m) :=
  existsUnique_mW (by norm_num) _ (by simp)

/-- The equation of `m^W` at spectrum `(1, −1)`, `z = i`. -/
example : 0 < (mW (![1, -1] : Fin 2 → ℝ) Complex.I).im ∧
    mW (![1, -1] : Fin 2 → ℝ) Complex.I =
      stieltjesA (![1, -1] : Fin 2 → ℝ) (Complex.I + mW (![1, -1] : Fin 2 → ℝ) Complex.I) :=
  mW_spec (by norm_num) _ (by simp)

/-- The lower bound on `Im m^W` at `N = 2`, spectrum `(1, −1)`, `τ = 1/2`, `z = i/2`. -/
example : ((3 * (1 / 2 : ℝ)⁻¹ + 1) ^ 2)⁻¹ * (Complex.I / 2).im ≤
    (mW (![1, -1] : Fin 2 → ℝ) (Complex.I / 2)).im :=
  im_mW_ge (by norm_num) (by norm_num) (fun i => by fin_cases i <;> norm_num) (by simp)
    (by simp) (by norm_num)

/-- The derivative of `m^W` at spectrum `(1, −1)`, `z = i`. -/
example : ∃ m' : ℂ, HasDerivAt (mW (![1, -1] : Fin 2 → ℝ)) m' Complex.I ∧
    ‖m'‖ ≤ (mW (![1, -1] : Fin 2 → ℝ) Complex.I).im / Complex.I.im :=
  hasDerivAt_mW (by norm_num) _ (by simp)

/-- Monotonicity of `Ψ^W` at spectrum `(1, −1)`, `E = 0`, between `η = 1/2` and `η = 1`. -/
example : PsiW (![1, -1] : Fin 2 → ℝ) ⟨0, 1⟩ ≤ PsiW (![1, -1] : Fin 2 → ℝ) ⟨0, 1 / 2⟩ :=
  PsiW_anti (by norm_num) _ 0 (by norm_num) (by norm_num)

#print axioms Anisotropic.PsiW
#print axioms Anisotropic.existsUnique_mW
#print axioms Anisotropic.mW_spec
#print axioms Anisotropic.mW_eq_of_spec
#print axioms Anisotropic.im_mW_ge
#print axioms Anisotropic.hasDerivAt_mW
#print axioms Anisotropic.PsiW_anti

end Anisotropic
