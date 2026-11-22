module

public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.EdgeDefs
public import Anisotropic.Wigner.EdgeGap
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.SelfConsistent

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Square-root behaviour of `Im m^W` near `L±`, the continuation of `m^W` across `(L₊, ∞)`, and the counterpart of (tur2) for `m^W` -/

/-- `S(maxᵢ aᵢ + 1) ≤ 1`. -/
private lemma edgeSqrt_sW_le_one {N : ℕ} (a : Fin N → ℝ) : sW a ((⨆ i, a i) + 1) ≤ 1 := by
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

/-- `S` is continuous at every point to the right of the spectrum. -/
private lemma edgeSqrt_sW_continuousAt {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hx : ∀ i, a i < x) :
    ContinuousAt (sW a) x := by
  unfold sW
  refine continuousAt_const.mul (tendsto_finsetSum _ fun i _ => ?_)
  have hne : (a i - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (hx i).ne)
  exact ((continuousAt_const.sub continuousAt_id).pow 2).inv₀ hne

/-- Under `|aᵢ| ≤ τ⁻¹ − 2` and `maxᵢ aᵢ + τ/4 ≤ x₊`: `τ/4 ≤ x₊ − aᵢ ≤ 2/τ` and `S(x₊) = 1`. -/
private lemma edgeSqrt_xp_facts {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {a : Fin N → ℝ}
    (ha : ∀ i, |a i| ≤ τ⁻¹ - 2) (hgap : (⨆ i, a i) + τ / 4 ≤ xpW a) :
    (∀ i, τ / 4 ≤ xpW a - a i) ∧ (∀ i, xpW a - a i ≤ 2 / τ) ∧ sW a (xpW a) = 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set α := ⨆ i, a i with hα
  have hle : ∀ i, a i ≤ α := fun i => le_ciSup (Set.finite_range a).bddAbove i
  set T := {x | α < x ∧ sW a x ≤ 1} with hT
  have hbdd : BddBelow T := ⟨α, fun x hx => hx.1.le⟩
  have hmem : α + 1 ∈ T := ⟨by linarith, edgeSqrt_sW_le_one a⟩
  have hxp : xpW a = sInf T := rfl
  have hup : xpW a ≤ α + 1 := hxp ▸ csInf_le hbdd hmem
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  have hα1 := abs_le.1 (ha i₀)
  rw [hi₀] at hα1
  refine ⟨fun i => by linarith [hle i], fun i => ?_, ?_⟩
  · have := abs_le.1 (ha i)
    have h2 : (2 : ℝ) / τ = 2 * τ⁻¹ := by ring
    linarith
  have hgt : ∀ i, a i < xpW a := fun i => by linarith [hle i]
  have hc := edgeSqrt_sW_continuousAt a hgt
  apply le_antisymm
  · by_contra h
    push Not at h
    have hev : ∀ᶠ y in 𝓝 (xpW a), 1 < sW a y := hc.eventually (lt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨y, hyT, hy⟩ := exists_lt_of_csInf_lt ⟨α + 1, hmem⟩
      (show sInf T < xpW a + δ by rw [← hxp]; linarith)
    have hy1 : xpW a ≤ y := hxp ▸ csInf_le hbdd hyT
    have : dist y (xpW a) < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    linarith [hball this, hyT.2]
  · by_contra h
    push Not at h
    have hev : ∀ᶠ y in 𝓝 (xpW a), sW a y < 1 := hc.eventually (gt_mem_nhds h)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set y := xpW a - min (δ / 2) (τ / 8) with hy
    have hm1 : 0 < min (δ / 2) (τ / 8) := lt_min (by linarith) (by linarith)
    have hm2 : min (δ / 2) (τ / 8) ≤ δ / 2 := min_le_left _ _
    have hm3 : min (δ / 2) (τ / 8) ≤ τ / 8 := min_le_right _ _
    have hyd : dist y (xpW a) < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hyT : y ∈ T := ⟨by linarith, (hball hyd).le⟩
    have := hxp ▸ csInf_le hbdd hyT
    linarith

/-- Real and imaginary parts of `m_A(w)`. -/
private lemma edgeSqrt_stieltjesA_re_im {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    (stieltjesA a w).re = (N : ℝ)⁻¹ * ∑ i, (a i - w.re) / ((a i - w.re) ^ 2 + w.im ^ 2) ∧
    (stieltjesA a w).im = (N : ℝ)⁻¹ * ∑ i, w.im / ((a i - w.re) ^ 2 + w.im ^ 2) := by
  unfold stieltjesA
  rw [show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, Complex.re_sum, Complex.im_sum]
  constructor <;> congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring
  · rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring

/-- `P = N⁻¹ ∑ᵢ eᵢ / (eᵢ² |eᵢ + u|²)` with `eᵢ = x − aᵢ`, `u = p + iq`. -/
private def edgeSqrt_P {N : ℕ} (a : Fin N → ℝ) (x p q : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (x - a i) / ((x - a i) ^ 2 * ((x - a i + p) ^ 2 + q ^ 2))

/-- `Q = N⁻¹ ∑ᵢ 1 / (eᵢ² |eᵢ + u|²)` with `eᵢ = x − aᵢ`, `u = p + iq`. -/
private def edgeSqrt_Q {N : ℕ} (a : Fin N → ℝ) (x p q : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, 1 / ((x - a i) ^ 2 * ((x - a i + p) ^ 2 + q ^ 2))

/-- `S(x + u) = N⁻¹ ∑ᵢ 1 / |eᵢ + u|²` with `eᵢ = x − aᵢ`, `u = p + iq`. -/
private def edgeSqrt_S {N : ℕ} (a : Fin N → ℝ) (x p q : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, 1 / ((x - a i + p) ^ 2 + q ^ 2)

/-- Exact form of `g(x + u) − g(x)` and of `Im m_A(x + u)` when `S(x) = 1`, `u = p + iq`:
`Re g − g(x) = (p² − q²) P + p |u|² Q`, `Im g = q (2pP + |u|² Q)`, `Im m_A = q S(x + u)`. -/
private lemma edgeSqrt_identity {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hS : sW a x = 1)
    (hx : ∀ i, a i < x) (p q : ℝ) (hD : ∀ i, 0 < (x - a i + p) ^ 2 + q ^ 2) :
    ((⟨x + p, q⟩ : ℂ) - stieltjesA a ⟨x + p, q⟩).re - gW a x =
        (p ^ 2 - q ^ 2) * edgeSqrt_P a x p q + p * (p ^ 2 + q ^ 2) * edgeSqrt_Q a x p q ∧
      ((⟨x + p, q⟩ : ℂ) - stieltjesA a ⟨x + p, q⟩).im =
        q * (2 * p * edgeSqrt_P a x p q + (p ^ 2 + q ^ 2) * edgeSqrt_Q a x p q) ∧
      (stieltjesA a ⟨x + p, q⟩).im = q * edgeSqrt_S a x p q := by
  obtain ⟨hre, him⟩ := edgeSqrt_stieltjesA_re_im a ⟨x + p, q⟩
  simp only at hre him
  have hS' : (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹ = 1 := hS
  have he : ∀ i, x - a i ≠ 0 := fun i => (sub_pos.2 (hx i)).ne'
  have hD' : ∀ i, (a i - (x + p)) ^ 2 + q ^ 2 ≠ 0 := fun i => by
    have := hD i
    have e : (a i - (x + p)) ^ 2 = (x - a i + p) ^ 2 := by ring
    rw [e]; exact this.ne'
  refine ⟨?_, ?_, ?_⟩
  · have hsum : ∑ i, (p * ((a i - x) ^ 2)⁻¹ - (a i - (x + p)) / ((a i - (x + p)) ^ 2 + q ^ 2) +
        (a i - x)⁻¹) = ∑ i, ((p ^ 2 - q ^ 2) * ((x - a i) / ((x - a i) ^ 2 *
          ((x - a i + p) ^ 2 + q ^ 2))) + p * (p ^ 2 + q ^ 2) * (1 / ((x - a i) ^ 2 *
          ((x - a i + p) ^ 2 + q ^ 2)))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := he i
      have h2 := hD' i
      have h3 := (hD i).ne'
      have h4 : a i - x ≠ 0 := fun h => h1 (by linarith)
      field_simp
      ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    rw [Complex.sub_re, hre, edgeSqrt_P, edgeSqrt_Q, gW]
    simp only
    linear_combination (-p) * hS' + (N : ℝ)⁻¹ * hsum
  · have hsum : ∑ i, (q * ((a i - x) ^ 2)⁻¹ - q / ((a i - (x + p)) ^ 2 + q ^ 2)) =
        ∑ i, (q * (2 * p * ((x - a i) / ((x - a i) ^ 2 * ((x - a i + p) ^ 2 + q ^ 2))) +
          (p ^ 2 + q ^ 2) * (1 / ((x - a i) ^ 2 * ((x - a i + p) ^ 2 + q ^ 2))))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := he i
      have h2 := hD' i
      have h3 := (hD i).ne'
      have h4 : a i - x ≠ 0 := fun h => h1 (by linarith)
      field_simp
      ring
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    rw [Complex.sub_im, him, edgeSqrt_P, edgeSqrt_Q]
    simp only
    linear_combination (-q) * hS' + (N : ℝ)⁻¹ * hsum
  · rw [him, edgeSqrt_S, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (a i - (x + p)) ^ 2 = (x - a i + p) ^ 2 := by ring
    rw [e]
    ring

/-- Averages against the weights `(aᵢ − x)⁻²` when `S(x) = 1`: an upper bound. -/
private lemma edgeSqrt_avg_le {N : ℕ} (a : Fin N → ℝ) {x c : ℝ} (hS : sW a x = 1)
    (t : Fin N → ℝ) (h : ∀ i, t i ≤ c * ((a i - x) ^ 2)⁻¹) : (N : ℝ)⁻¹ * ∑ i, t i ≤ c := by
  have hS' : (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹ = 1 := hS
  calc (N : ℝ)⁻¹ * ∑ i, t i ≤ (N : ℝ)⁻¹ * ∑ i, c * ((a i - x) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)
    _ = c * ((N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹) := by rw [← Finset.mul_sum]; ring
    _ = c := by rw [hS', mul_one]

/-- Averages against the weights `(aᵢ − x)⁻²` when `S(x) = 1`: a lower bound. -/
private lemma edgeSqrt_avg_ge {N : ℕ} (a : Fin N → ℝ) {x c : ℝ} (hS : sW a x = 1)
    (t : Fin N → ℝ) (h : ∀ i, c * ((a i - x) ^ 2)⁻¹ ≤ t i) : c ≤ (N : ℝ)⁻¹ * ∑ i, t i := by
  have hS' : (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹ = 1 := hS
  calc c = c * ((N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹) := by rw [hS', mul_one]
    _ = (N : ℝ)⁻¹ * ∑ i, c * ((a i - x) ^ 2)⁻¹ := by rw [← Finset.mul_sum]; ring
    _ ≤ (N : ℝ)⁻¹ * ∑ i, t i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)

/-- `e²/2 ≤ (e + p)² + q² ≤ 2e²` for `|p|, |q| ≤ e/4`. -/
private lemma edgeSqrt_D_bounds {e p q : ℝ} (he : 0 < e) (hp : |p| ≤ e / 4) (hq : |q| ≤ e / 4) :
    e ^ 2 / 2 ≤ (e + p) ^ 2 + q ^ 2 ∧ (e + p) ^ 2 + q ^ 2 ≤ 2 * e ^ 2 := by
  obtain ⟨hp1, hp2⟩ := abs_le.1 hp
  obtain ⟨hq1, hq2⟩ := abs_le.1 hq
  constructor
  · nlinarith [sq_nonneg q]
  · nlinarith

/-- Bounds on `P`, `Q` and `S(x + u)` for `|p|, |q| ≤ τ/16` when `τ/4 ≤ x − aᵢ ≤ 2/τ` and
`S(x) = 1`: `τ/4 ≤ P ≤ 8/τ`, `(τ/2) P ≤ Q ≤ (4/τ) P` and `1/2 ≤ S(x + u) ≤ 2`. -/
private lemma edgeSqrt_PQS_bounds {N : ℕ} (a : Fin N → ℝ) {x τ : ℝ} (hτ : 0 < τ)
    (hS : sW a x = 1) (he1 : ∀ i, τ / 4 ≤ x - a i) (he2 : ∀ i, x - a i ≤ 2 / τ) {p q : ℝ}
    (hp : |p| ≤ τ / 16) (hq : |q| ≤ τ / 16) :
    τ / 4 ≤ edgeSqrt_P a x p q ∧ edgeSqrt_P a x p q ≤ 8 / τ ∧
      τ / 2 * edgeSqrt_P a x p q ≤ edgeSqrt_Q a x p q ∧
      edgeSqrt_Q a x p q ≤ 4 / τ * edgeSqrt_P a x p q ∧
      1 / 2 ≤ edgeSqrt_S a x p q ∧ edgeSqrt_S a x p q ≤ 2 := by
  have key : ∀ i, (0 < x - a i ∧ ((a i - x) ^ 2)⁻¹ = ((x - a i) ^ 2)⁻¹) ∧
      (x - a i) ^ 2 / 2 ≤ (x - a i + p) ^ 2 + q ^ 2 ∧
      (x - a i + p) ^ 2 + q ^ 2 ≤ 2 * (x - a i) ^ 2 := fun i => by
    have h0 : 0 < x - a i := by linarith [he1 i]
    have hp' : |p| ≤ (x - a i) / 4 := by linarith [he1 i]
    have hq' : |q| ≤ (x - a i) / 4 := by linarith [he1 i]
    exact ⟨⟨h0, by ring_nf⟩, edgeSqrt_D_bounds h0 hp' hq'⟩
  have hNP : 0 ≤ (N : ℝ)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply edgeSqrt_avg_ge a hS
    intro i
    obtain ⟨⟨h0, hr⟩, hD1, hD2⟩ := key i
    rw [hr]
    have h2 := he2 i
    set e := x - a i
    set D := (e + p) ^ 2 + q ^ 2
    have hDp : 0 < D := by nlinarith
    have : τ * e ≤ 2 := by rw [le_div_iff₀ hτ] at h2; linarith
    have h3 : τ / 4 ≤ e / D := by rw [le_div_iff₀ hDp]; nlinarith
    calc τ / 4 * (e ^ 2)⁻¹ = (e ^ 2)⁻¹ * (τ / 4) := mul_comm _ _
      _ ≤ (e ^ 2)⁻¹ * (e / D) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = e / (e ^ 2 * D) := by field_simp
  · apply edgeSqrt_avg_le a hS
    intro i
    obtain ⟨⟨h0, hr⟩, hD1, hD2⟩ := key i
    rw [hr]
    have h1 := he1 i
    set e := x - a i
    set D := (e + p) ^ 2 + q ^ 2
    have hDp : 0 < D := by nlinarith
    have h3 : e / D ≤ 8 / τ := by
      rw [div_le_div_iff₀ hDp hτ]; nlinarith
    calc e / (e ^ 2 * D) = (e ^ 2)⁻¹ * (e / D) := by field_simp
      _ ≤ (e ^ 2)⁻¹ * (8 / τ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 8 / τ * (e ^ 2)⁻¹ := mul_comm _ _
  · unfold edgeSqrt_P edgeSqrt_Q
    rw [← mul_assoc, mul_comm (τ / 2), mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hNP
    obtain ⟨⟨h0, hr⟩, hD1, hD2⟩ := key i
    have h2 := he2 i
    set e := x - a i
    set D := (e + p) ^ 2 + q ^ 2
    have hDp : 0 < D := by nlinarith
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    have : τ * e ≤ 2 := by rw [le_div_iff₀ hτ] at h2; linarith
    linarith
  · unfold edgeSqrt_P edgeSqrt_Q
    conv_rhs => rw [mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hNP
    obtain ⟨⟨h0, hr⟩, hD1, hD2⟩ := key i
    have h1 := he1 i
    set e := x - a i
    set D := (e + p) ^ 2 + q ^ 2
    have hDp : 0 < D := by nlinarith
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
    linarith
  · apply edgeSqrt_avg_ge a hS
    intro i
    obtain ⟨⟨h0, hr⟩, hD1, hD2⟩ := key i
    rw [hr]
    set e := x - a i
    set D := (e + p) ^ 2 + q ^ 2
    have hDp : 0 < D := by nlinarith
    rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · apply edgeSqrt_avg_le a hS
    intro i
    obtain ⟨⟨h0, hr⟩, hD1, hD2⟩ := key i
    rw [hr]
    set e := x - a i
    set D := (e + p) ^ 2 + q ^ 2
    have hDp : 0 < D := by nlinarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The two regimes for `u = p + iq`, `q > 0`, given `P > 0`, `Q ≥ 0`, `|u| ≤ ρ`, `ρ Q ≤ P/4` and
`η = q (2pP + |u|² Q) > 0`, with `Δ = (p² − q²) P + p |u|² Q`: `|Δ| + η ≍ |u|² P`; `Δ ≤ 0` forces
`q² ≥ |u|²/2`; `Δ ≥ 0` forces `p > 0`, `p² ≥ 3|u|²/8` and `2pP + |u|² Q ≤ (8/3) pP`. -/
private lemma edgeSqrt_cases {p q P Q ρ : ℝ} (hq : 0 < q) (hP : 0 < P) (hQ : 0 ≤ Q)
    (hρ : 0 ≤ ρ) (hpq : p ^ 2 + q ^ 2 ≤ ρ ^ 2) (hρQ : ρ * Q ≤ P / 4)
    (hη : 0 < q * (2 * p * P + (p ^ 2 + q ^ 2) * Q)) :
    (3 / 4 * (p ^ 2 + q ^ 2) * P ≤ |(p ^ 2 - q ^ 2) * P + p * (p ^ 2 + q ^ 2) * Q| +
        q * (2 * p * P + (p ^ 2 + q ^ 2) * Q) ∧
      |(p ^ 2 - q ^ 2) * P + p * (p ^ 2 + q ^ 2) * Q| + q * (2 * p * P + (p ^ 2 + q ^ 2) * Q) ≤
        3 * (p ^ 2 + q ^ 2) * P) ∧
    ((p ^ 2 - q ^ 2) * P + p * (p ^ 2 + q ^ 2) * Q ≤ 0 → (p ^ 2 + q ^ 2) / 2 ≤ q ^ 2) ∧
    (0 ≤ (p ^ 2 - q ^ 2) * P + p * (p ^ 2 + q ^ 2) * Q → 0 < p ∧
      3 / 8 * (p ^ 2 + q ^ 2) ≤ p ^ 2 ∧ 2 * p * P + (p ^ 2 + q ^ 2) * Q ≤ 8 / 3 * (p * P)) := by
  set n2 := p ^ 2 + q ^ 2 with hn2
  set Δ := (p ^ 2 - q ^ 2) * P + p * n2 * Q with hΔ
  set s := 2 * p * P + n2 * Q with hsdef
  have hn2pos : 0 < n2 := by positivity
  have hs : 0 < s := by
    by_contra h
    push Not at h
    nlinarith
  have hpabs : |p| ≤ ρ :=
    (pow_le_pow_iff_left₀ (abs_nonneg p) hρ two_ne_zero).1 (by rw [sq_abs]; nlinarith)
  have hqρ : q ≤ ρ := (pow_le_pow_iff_left₀ hq.le hρ two_ne_zero).1 (by nlinarith)
  have hpQ : |p| * Q ≤ P / 4 := le_trans (mul_le_mul_of_nonneg_right hpabs hQ) hρQ
  have hqQ : q * Q ≤ P / 4 := le_trans (mul_le_mul_of_nonneg_right hqρ hQ) hρQ
  have hpp : p ≤ |p| := le_abs_self p
  have hpm : -|p| ≤ p := neg_abs_le p
  have hsq : |p| ^ 2 = p ^ 2 := sq_abs p
  have h2pq : 2 * |p| * q ≤ n2 := by nlinarith [sq_nonneg (|p| - q)]
  have hpq2 : |p ^ 2 - q ^ 2| ≤ n2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hsmall : p ≤ 0 → 64 * p ^ 2 < n2 := by
    intro hp0
    have h0 : 2 * |p| * P < n2 * Q := by rw [abs_of_nonpos hp0]; linarith
    have h1 : (2 * |p| * P) ^ 2 < (n2 * Q) ^ 2 :=
      pow_lt_pow_left₀ h0 (by positivity) two_ne_zero
    have h3 : n2 * Q ^ 2 ≤ (ρ * Q) ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right hpq (sq_nonneg Q)
    have h4 : (ρ * Q) ^ 2 ≤ (P / 4) ^ 2 := pow_le_pow_left₀ (by positivity) hρQ 2
    have h2 : (n2 * Q) ^ 2 ≤ n2 * (P / 4) ^ 2 := by
      have : (n2 * Q) ^ 2 = n2 * (n2 * Q ^ 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (h3.trans h4) hn2pos.le
    rw [mul_pow, mul_pow, hsq] at h1
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg P)]
  have hΔabs : |Δ| ≤ 5 / 4 * n2 * P := by
    calc |Δ| ≤ |(p ^ 2 - q ^ 2) * P| + |p * n2 * Q| := abs_add_le _ _
      _ = |p ^ 2 - q ^ 2| * P + n2 * (|p| * Q) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hP, abs_of_pos hn2pos, abs_of_nonneg hQ]
          ring
      _ ≤ n2 * P + n2 * (P / 4) := by
          gcongr
      _ = 5 / 4 * n2 * P := by ring
  have hηle : q * s ≤ 5 / 4 * n2 * P := by
    have e : q * s = 2 * p * q * P + n2 * (q * Q) := by rw [hsdef]; ring
    have h1 : 2 * p * q * P ≤ n2 * P := by
      have : 2 * p * q ≤ n2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hP.le
    have h2 : n2 * (q * Q) ≤ n2 * (P / 4) := mul_le_mul_of_nonneg_left hqQ hn2pos.le
    linarith
  refine ⟨⟨?_, by linarith⟩, ?_, ?_⟩
  · have hid : Δ * (p ^ 2 - q ^ 2) + 2 * p * q * (q * s) = n2 ^ 2 * (P + p * Q) := by
      rw [hΔ, hsdef, hn2]; ring
    have hb : |Δ * (p ^ 2 - q ^ 2) + 2 * p * q * (q * s)| ≤ n2 * (|Δ| + q * s) := by
      calc |Δ * (p ^ 2 - q ^ 2) + 2 * p * q * (q * s)|
          ≤ |Δ * (p ^ 2 - q ^ 2)| + |2 * p * q * (q * s)| := abs_add_le _ _
        _ = |Δ| * |p ^ 2 - q ^ 2| + (2 * |p| * q) * (q * s) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hq,
              abs_of_pos (mul_pos hq hs)]
            norm_num
        _ ≤ |Δ| * n2 + n2 * (q * s) := by
            gcongr
        _ = n2 * (|Δ| + q * s) := by ring
    have hPQ : 3 / 4 * P ≤ P + p * Q := by nlinarith
    rw [hid, abs_of_nonneg (by nlinarith)] at hb
    have : n2 * (3 / 4 * n2 * P) ≤ n2 * (|Δ| + q * s) := by nlinarith
    exact le_of_mul_le_mul_left (by linarith) hn2pos
  · intro hΔ0
    rcases le_or_gt p 0 with hp0 | hp0
    · have := hsmall hp0
      linarith [sq_nonneg p]
    · have h1 : (p ^ 2 - q ^ 2) * P ≤ 0 := by
        have : 0 ≤ p * n2 * Q := by positivity
        linarith
      have : p ^ 2 - q ^ 2 ≤ 0 := by
        by_contra h
        push Not at h
        linarith [mul_pos h hP]
      linarith
  · intro hΔ0
    have hp0 : 0 < p := by
      by_contra hp0
      push Not at hp0
      have h1 := hsmall hp0
      have h2 : 0 ≤ (p ^ 2 - q ^ 2) * P := by
        have : p * n2 * Q ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hp0 hn2pos.le) hQ
        linarith
      have : 0 ≤ p ^ 2 - q ^ 2 := by
        by_contra h
        push Not at h
        linarith [mul_neg_of_neg_of_pos h hP]
      linarith [sq_nonneg p]
    have hpQ' : p * Q ≤ P / 4 := by rw [abs_of_pos hp0] at hpQ; exact hpQ
    have h38 : 3 / 8 * n2 ≤ p ^ 2 := by
      have h1 : -(n2 * (P / 4)) ≤ (p ^ 2 - q ^ 2) * P := by
        have : p * n2 * Q ≤ n2 * (P / 4) := by
          have := mul_le_mul_of_nonneg_left hpQ' hn2pos.le
          linarith
        linarith
      have : -(n2 / 4) ≤ p ^ 2 - q ^ 2 := by
        by_contra h
        push Not at h
        have key : (p ^ 2 - q ^ 2 + n2 / 4) * P < 0 := mul_neg_of_neg_of_pos (by linarith) hP
        linarith
      linarith
    refine ⟨hp0, h38, ?_⟩
    have h1 : n2 * Q ≤ 8 / 3 * p * (p * Q) := by
      have : n2 ≤ 8 / 3 * p ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_right this hQ
      linarith
    have h2 : 8 / 3 * p * (p * Q) ≤ 8 / 3 * p * (P / 4) :=
      mul_le_mul_of_nonneg_left hpQ' (by positivity)
    linarith

/-- `K⁻¹ √X ≤ y` from `X ≤ K² y²`. -/
private lemma edgeSqrt_sqrt_lower {K X y : ℝ} (hK : 0 < K) (hy : 0 ≤ y) (h : X ≤ K ^ 2 * y ^ 2) :
    K⁻¹ * √X ≤ y := by
  rw [inv_mul_le_iff₀ hK]
  calc √X ≤ √((K * y) ^ 2) := Real.sqrt_le_sqrt (by rw [mul_pow]; exact h)
    _ = K * y := Real.sqrt_sq (by positivity)

/-- `y ≤ K √X` from `y² ≤ K² X`. -/
private lemma edgeSqrt_sqrt_upper {K X y : ℝ} (hK : 0 < K) (hy : 0 ≤ y)
    (h : y ^ 2 ≤ K ^ 2 * X) : y ≤ K * √X := by
  calc y = √(y ^ 2) := (Real.sqrt_sq hy).symm
    _ ≤ √(K ^ 2 * X) := Real.sqrt_le_sqrt h
    _ = K * √X := by rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK.le]

/-- `K⁻¹ (η/√X) ≤ y` from `η² ≤ K² y² X`. -/
private lemma edgeSqrt_div_lower {K X η y : ℝ} (hK : 0 < K) (hX : 0 < X) (hy : 0 ≤ y)
    (h : η ^ 2 ≤ K ^ 2 * y ^ 2 * X) : K⁻¹ * (η / √X) ≤ y := by
  have hs : 0 < √X := Real.sqrt_pos.2 hX
  rw [inv_mul_le_iff₀ hK, div_le_iff₀ hs]
  calc η ≤ |η| := le_abs_self η
    _ = √(η ^ 2) := (Real.sqrt_sq_eq_abs η).symm
    _ ≤ √((K * y) ^ 2 * X) := Real.sqrt_le_sqrt (by rw [mul_pow]; exact h)
    _ = K * y * √X := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- `y ≤ K (η/√X)` from `y² X ≤ K² η²`, `η ≥ 0`. -/
private lemma edgeSqrt_div_upper {K X η y : ℝ} (hK : 0 < K) (hX : 0 < X) (hη : 0 ≤ η)
    (hy : 0 ≤ y) (h : y ^ 2 * X ≤ K ^ 2 * η ^ 2) : y ≤ K * (η / √X) := by
  have hs : 0 < √X := Real.sqrt_pos.2 hX
  rw [mul_div_assoc', le_div_iff₀ hs]
  calc y * √X = √((y ^ 2) * X) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hy]
    _ ≤ √((K * η) ^ 2) := Real.sqrt_le_sqrt (by rw [mul_pow]; exact h)
    _ = K * η := Real.sqrt_sq (by positivity)

/-- Arithmetic for the regime `E ≤ L₊` with `K = 18/τ`. -/
private lemma edgeSqrt_arith_neg {τ P S q n2 X : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    (hP1 : τ / 4 ≤ P) (hτP : τ * P ≤ 8) (hS1 : 1 / 2 ≤ S) (hS2 : S ≤ 2)
    (hq2 : n2 / 2 ≤ q ^ 2) (hqn : q ^ 2 ≤ n2) (hX1 : 3 / 4 * n2 * P ≤ X) (hX2 : X ≤ 3 * n2 * P)
    (hn2 : 0 < n2) :
    X ≤ (18 / τ) ^ 2 * (q * S) ^ 2 ∧ (q * S) ^ 2 ≤ (18 / τ) ^ 2 * X := by
  have hK2 : (18 / τ) ^ 2 = 324 / τ ^ 2 := by rw [div_pow]; norm_num
  have hS0 : 0 ≤ S := by linarith
  have hSl : 1 / 4 ≤ S ^ 2 := by nlinarith
  have hSu : S ^ 2 ≤ 4 := by nlinarith
  have hqS1 : n2 / 8 ≤ (q * S) ^ 2 := by
    rw [mul_pow]
    calc n2 / 8 = n2 / 2 * (1 / 4) := by ring
      _ ≤ q ^ 2 * S ^ 2 := mul_le_mul hq2 hSl (by norm_num) (sq_nonneg q)
  have hqS2 : (q * S) ^ 2 ≤ 4 * n2 := by
    rw [mul_pow]
    calc q ^ 2 * S ^ 2 ≤ n2 * 4 := mul_le_mul hqn hSu (sq_nonneg S) hn2.le
      _ = 4 * n2 := by ring
  have hτ2' : τ ^ 2 ≤ τ / 2 := by nlinarith
  constructor
  · have h1 : 24 * P ≤ 324 / τ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : τ * P * τ ≤ 8 * (1 / 2) := mul_le_mul hτP hτ2 hτ.le (by norm_num)
      nlinarith
    calc X ≤ 3 * n2 * P := hX2
      _ = n2 / 8 * (24 * P) := by ring
      _ ≤ (q * S) ^ 2 * (324 / τ ^ 2) := mul_le_mul hqS1 h1 (by linarith) (by positivity)
      _ = (18 / τ) ^ 2 * (q * S) ^ 2 := by rw [hK2]; ring
  · have h1 : 16 / 3 ≤ 324 / τ ^ 2 * P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : τ ^ 2 ≤ 4 * P * τ := by nlinarith
      nlinarith
    calc (q * S) ^ 2 ≤ 4 * n2 := hqS2
      _ = 3 / 4 * n2 * (16 / 3) := by ring
      _ ≤ 3 / 4 * n2 * (324 / τ ^ 2 * P) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 324 / τ ^ 2 * (3 / 4 * n2 * P) := by ring
      _ ≤ 324 / τ ^ 2 * X := mul_le_mul_of_nonneg_left hX1 (by positivity)
      _ = (18 / τ) ^ 2 * X := by rw [hK2]

/-- Arithmetic for the regime `E ≥ L₊` with `K = 18/τ`. -/
private lemma edgeSqrt_arith_pos {τ P S p s n2 X : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    (hP1 : τ / 4 ≤ P) (hτP : τ * P ≤ 8) (hS1 : 1 / 2 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 < p)
    (hp2 : 3 / 8 * n2 ≤ p ^ 2) (hpn : p ^ 2 ≤ n2) (hs1 : 2 * p * P ≤ s)
    (hs2 : s ≤ 8 / 3 * (p * P)) (hX1 : 3 / 4 * n2 * P ≤ X) (hX2 : X ≤ 3 * n2 * P) :
    s ^ 2 ≤ (18 / τ) ^ 2 * S ^ 2 * X ∧ S ^ 2 * X ≤ (18 / τ) ^ 2 * s ^ 2 := by
  have hK2 : (18 / τ) ^ 2 = 324 / τ ^ 2 := by rw [div_pow]; norm_num
  have hPpos : 0 < P := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hSl : 1 / 4 ≤ S ^ 2 := by nlinarith
  have hSu : S ^ 2 ≤ 4 := by nlinarith
  have hs0 : 0 ≤ s := le_trans (by positivity) hs1
  have hn0 : 0 ≤ n2 := le_trans (sq_nonneg p) hpn
  constructor
  · have h1 : s ^ 2 ≤ 64 / 9 * n2 * P ^ 2 := by
      have : s ^ 2 ≤ (8 / 3 * (p * P)) ^ 2 := pow_le_pow_left₀ hs0 hs2 2
      have h2 : (8 / 3 * (p * P)) ^ 2 = 64 / 9 * p ^ 2 * P ^ 2 := by ring
      have h3 : 64 / 9 * p ^ 2 * P ^ 2 ≤ 64 / 9 * n2 * P ^ 2 := by gcongr
      linarith
    have h2 : 1024 / 27 * P ≤ 324 / τ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : τ * P * τ ≤ 8 * (1 / 2) := mul_le_mul hτP hτ2 hτ.le (by norm_num)
      nlinarith
    calc s ^ 2 ≤ 64 / 9 * n2 * P ^ 2 := h1
      _ = 1 / 4 * (3 / 4 * n2 * P) * (1024 / 27 * P) := by ring
      _ ≤ S ^ 2 * X * (324 / τ ^ 2) := by
          have hX0 : 0 ≤ X := le_trans (by positivity) hX1
          apply mul_le_mul (mul_le_mul hSl hX1 (by positivity) (by positivity)) h2
            (by positivity) (by positivity)
      _ = (18 / τ) ^ 2 * S ^ 2 * X := by rw [hK2]; ring
  · have h1 : 3 / 2 * n2 * P ^ 2 ≤ s ^ 2 := by
      have : (2 * p * P) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs1 2
      have h2 : (2 * p * P) ^ 2 = 4 * p ^ 2 * P ^ 2 := by ring
      have h3 : 4 * (3 / 8 * n2) * P ^ 2 ≤ 4 * p ^ 2 * P ^ 2 := by gcongr
      linarith
    have h2 : 8 ≤ 324 / τ ^ 2 * P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : τ ^ 2 ≤ 4 * P * τ := by nlinarith
      nlinarith
    calc S ^ 2 * X ≤ 4 * (3 * n2 * P) := mul_le_mul hSu hX2 (by linarith) (by norm_num)
      _ = 3 / 2 * n2 * P * 8 := by ring
      _ ≤ 3 / 2 * n2 * P * (324 / τ ^ 2 * P) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 324 / τ ^ 2 * (3 / 2 * n2 * P ^ 2) := by ring
      _ ≤ 324 / τ ^ 2 * s ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (18 / τ) ^ 2 * s ^ 2 := by rw [hK2]

/-- Local form of the square-root edge (§12.4): for `w` with `|w − x₊| ≤ τ/16`, `Im w > 0` and
`Im g(w) > 0`, with `z = g(w)` and `Im m_A(w) = Im(w − z)`:
`(3τ/16) |w − x₊|² ≤ |E − L₊| + η`, and with `K = 18/τ`, `Im m_A(w) ≍ √(κ + η)` for `E ≤ L₊`,
`Im m_A(w) ≍ η/√(κ + η)` for `E ≥ L₊`. -/
private lemma edgeSqrt_local {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) {a : Fin N → ℝ}
    {x : ℝ} (he1 : ∀ i, τ / 4 ≤ x - a i) (he2 : ∀ i, x - a i ≤ 2 / τ) (hS : sW a x = 1)
    (w : ℂ) (hw : ‖w - x‖ ≤ τ / 16) (hq : 0 < w.im) (hz : 0 < (w - stieltjesA a w).im) :
    3 * τ / 16 * ‖w - x‖ ^ 2 ≤ |(w - stieltjesA a w).re - gW a x| + (w - stieltjesA a w).im ∧
    ((w - stieltjesA a w).re ≤ gW a x →
      (18 / τ)⁻¹ * √(gW a x - (w - stieltjesA a w).re + (w - stieltjesA a w).im) ≤
          (stieltjesA a w).im ∧
        (stieltjesA a w).im ≤
          18 / τ * √(gW a x - (w - stieltjesA a w).re + (w - stieltjesA a w).im)) ∧
    (gW a x ≤ (w - stieltjesA a w).re →
      (18 / τ)⁻¹ * ((w - stieltjesA a w).im /
          √((w - stieltjesA a w).re - gW a x + (w - stieltjesA a w).im)) ≤ (stieltjesA a w).im ∧
        (stieltjesA a w).im ≤ 18 / τ * ((w - stieltjesA a w).im /
          √((w - stieltjesA a w).re - gW a x + (w - stieltjesA a w).im))) := by
  set p := w.re - x with hp
  set q := w.im with hqdef
  have hw' : w = ⟨x + p, q⟩ := Complex.ext (by simp [p]) rfl
  have hn : ‖w - x‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  have hpb : |p| ≤ τ / 16 := by
    have := Complex.abs_re_le_norm (w - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have hqb : |q| ≤ τ / 16 := by
    have := Complex.abs_im_le_norm (w - x)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  have hx : ∀ i, a i < x := fun i => by linarith [he1 i]
  have hD : ∀ i, 0 < (x - a i + p) ^ 2 + q ^ 2 := fun i => by
    have h0 : 0 < x - a i := by linarith [he1 i]
    have := (edgeSqrt_D_bounds (p := p) (q := q) h0 (by linarith [he1 i]) (by linarith [he1 i])).1
    have : 0 < (x - a i) ^ 2 / 2 := by positivity
    linarith
  obtain ⟨hre, him, hsim⟩ := edgeSqrt_identity a hS hx p q hD
  obtain ⟨hP1, hP2, hQ1, hQ2, hS1, hS2⟩ := edgeSqrt_PQS_bounds a hτ hS he1 he2 hpb hqb
  rw [← hw'] at hre him hsim
  set P := edgeSqrt_P a x p q
  set Q := edgeSqrt_Q a x p q
  set S := edgeSqrt_S a x p q
  have hPpos : 0 < P := by linarith
  have hQ0 : 0 ≤ Q := by nlinarith
  have hpq : p ^ 2 + q ^ 2 ≤ (τ / 16) ^ 2 := by
    rw [← hn]; exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hρQ : τ / 16 * Q ≤ P / 4 := by
    have : τ / 16 * (4 / τ * P) = P / 4 := by field_simp; ring
    calc τ / 16 * Q ≤ τ / 16 * (4 / τ * P) := mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = P / 4 := this
  have hη : 0 < q * (2 * p * P + (p ^ 2 + q ^ 2) * Q) := by rw [← him]; exact hz
  obtain ⟨⟨hX1, hX2⟩, hneg, hpos⟩ := edgeSqrt_cases hq hPpos hQ0 (by positivity) hpq hρQ hη
  rw [← hre, ← him] at hX1 hX2
  rw [← hre] at hneg hpos
  have hτP : τ * P ≤ 8 := by rw [le_div_iff₀ hτ] at hP2; linarith
  have hK : (0 : ℝ) < 18 / τ := by positivity
  have hSpos : 0 ≤ S := by linarith
  have hy : 0 ≤ q * S := by positivity
  set Δ := (w - stieltjesA a w).re - gW a x with hΔ
  set η := (w - stieltjesA a w).im with hηdef
  set n2 := p ^ 2 + q ^ 2 with hn2
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]
    have : 3 / 4 * n2 * (τ / 4) ≤ 3 / 4 * n2 * P :=
      mul_le_mul_of_nonneg_left hP1 (by positivity)
    linarith
  · intro hle
    have hΔ0 : Δ ≤ 0 := by rw [hΔ]; linarith
    have hq2 := hneg hΔ0
    have hX : gW a x - (w - stieltjesA a w).re + η = |Δ| + η := by
      rw [abs_of_nonpos hΔ0, hΔ]; ring
    rw [hX, hsim]
    have hqn : q ^ 2 ≤ n2 := by rw [hn2]; nlinarith
    obtain ⟨h1, h2⟩ := edgeSqrt_arith_neg hτ hτ2 hP1 hτP hS1 hS2 hq2 hqn hX1 hX2
      (by positivity)
    exact ⟨edgeSqrt_sqrt_lower hK hy h1, edgeSqrt_sqrt_upper hK hy h2⟩
  · intro hle
    have hΔ0 : 0 ≤ Δ := by rw [hΔ]; linarith
    obtain ⟨hp0, hp2, hs2⟩ := hpos hΔ0
    have hX : (w - stieltjesA a w).re - gW a x + η = |Δ| + η := by
      rw [abs_of_nonneg hΔ0, hΔ]
    have hXpos : 0 < |Δ| + η := by linarith
    have hs1 : 2 * p * P ≤ 2 * p * P + n2 * Q := by
      have : 0 ≤ n2 * Q := by positivity
      linarith
    have hpn : p ^ 2 ≤ n2 := by rw [hn2]; nlinarith
    obtain ⟨h1, h2⟩ := edgeSqrt_arith_pos hτ hτ2 hP1 hτP hS1 hS2 hp0 hp2 hpn hs1 hs2 hX1 hX2
    rw [hX, hsim]
    constructor
    · apply edgeSqrt_div_lower hK hXpos hy
      calc η ^ 2 = q ^ 2 * (2 * p * P + n2 * Q) ^ 2 := by rw [him]; ring
        _ ≤ q ^ 2 * ((18 / τ) ^ 2 * S ^ 2 * (|Δ| + η)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (18 / τ) ^ 2 * (q * S) ^ 2 * (|Δ| + η) := by ring
    · apply edgeSqrt_div_upper hK hXpos (by linarith) hy
      calc (q * S) ^ 2 * (|Δ| + η) = q ^ 2 * (S ^ 2 * (|Δ| + η)) := by ring
        _ ≤ q ^ 2 * ((18 / τ) ^ 2 * (2 * p * P + n2 * Q) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (18 / τ) ^ 2 * η ^ 2 := by rw [him]; ring

/-- `z ↦ z + m^W(z)` is continuous on `ℂ₊`. -/
private lemma edgeSqrt_continuousOn {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) :
    ContinuousOn (fun z => z + mW a z) {z : ℂ | 0 < z.im} := fun _ hz =>
  (continuousAt_id.add (hasDerivAt_mW hN a hz).choose_spec.1.continuousAt).continuousWithinAt

/-- Localization near `x₊` (§12.4): for `Im z > 0` and `|z − L₊| ≤ τ³/4096`, the solution
`w = z + m^W(z)` of `g(w) = z` satisfies `|w − x₊| < τ/16`. The set of such `z` where this holds
is open, and closed in the half-disc by the lower bound `(3τ/16)|w − x₊|² ≤ 2|z − L₊|`; it
contains `g(x₊ + iτ²/512)`. -/
private lemma edgeSqrt_boot {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    {a : Fin N → ℝ} (he1 : ∀ i, τ / 4 ≤ xpW a - a i) (he2 : ∀ i, xpW a - a i ≤ 2 / τ)
    (hS : sW a (xpW a) = 1) (z : ℂ) (hz : 0 < z.im) (hzc : ‖z - (LpW a : ℂ)‖ ≤ τ ^ 3 / 4096) :
    ‖z + mW a z - (xpW a : ℂ)‖ < τ / 16 := by
  set x := xpW a with hxdef
  have hL : LpW a = gW a x := rfl
  have hx : ∀ i, a i < x := fun i => by linarith [he1 i]
  have key : ∀ z : ℂ, 0 < z.im → ‖z - (LpW a : ℂ)‖ ≤ τ ^ 3 / 4096 →
      ‖z + mW a z - x‖ ≤ τ / 16 → ‖z + mW a z - x‖ < τ / 16 := by
    intro z hz hzc hw
    obtain ⟨hm, heq⟩ := mW_spec hN a hz
    have hwz : z + mW a z - stieltjesA a (z + mW a z) = z := by rw [← heq]; ring
    have hq : 0 < (z + mW a z).im := by rw [Complex.add_im]; linarith
    have hl := (edgeSqrt_local hτ hτ2 he1 he2 hS (z + mW a z) hw hq (by rw [hwz]; exact hz)).1
    rw [hwz, ← hL] at hl
    have h1 : |z.re - LpW a| ≤ ‖z - (LpW a : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (LpW a : ℂ))
      simpa using this
    have h2 : z.im ≤ ‖z - (LpW a : ℂ)‖ := by
      have := Complex.abs_im_le_norm (z - (LpW a : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith [le_abs_self z.im]
    have h3 : 3 * τ / 16 * ‖z + mW a z - x‖ ^ 2 ≤ 3 * τ / 16 * (τ ^ 2 / 384) := by
      have : 3 * τ / 16 * (τ ^ 2 / 384) = 2 * (τ ^ 3 / 4096) := by ring
      linarith
    have h4 : ‖z + mW a z - x‖ ^ 2 ≤ τ ^ 2 / 384 := le_of_mul_le_mul_left h3 (by positivity)
    have h5 : ‖z + mW a z - x‖ ^ 2 < (τ / 16) ^ 2 := by nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h5
  set F := fun z : ℂ => z + mW a z with hF
  set H := {z : ℂ | 0 < z.im} ∩ Metric.closedBall (LpW a : ℂ) (τ ^ 3 / 4096) with hH
  set U := {z : ℂ | 0 < z.im} ∩ F ⁻¹' Metric.ball (x : ℂ) (τ / 16) with hU
  have hpre : IsPreconnected H :=
    ((convex_halfSpace_im_gt 0).inter (convex_closedBall _ _)).isPreconnected
  have hcont := edgeSqrt_continuousOn hN a
  have hopen : IsOpen U := hcont.isOpen_inter_preimage (Complex.isOpen_im_gt 0) Metric.isOpen_ball
  -- a point of `H ∩ U`
  set δ := τ ^ 2 / 512 with hδ
  have hδpos : 0 < δ := by positivity
  have hδb : |δ| ≤ τ / 16 := by
    rw [abs_of_pos hδpos, hδ]
    have : τ ^ 2 ≤ τ / 2 := by nlinarith
    linarith
  have hD : ∀ i, 0 < (x - a i + 0) ^ 2 + δ ^ 2 := fun i => by positivity
  obtain ⟨hre, him, hsim⟩ := edgeSqrt_identity a hS hx 0 δ hD
  obtain ⟨hP1, hP2, hQ1, hQ2, hS1, hS2⟩ :=
    edgeSqrt_PQS_bounds a hτ hS he1 he2 (p := 0) (q := δ) (by rw [abs_zero]; positivity) hδb
  set w₀ : ℂ := ⟨x + 0, δ⟩ with hw₀
  set z₀ := w₀ - stieltjesA a w₀ with hz₀
  set P := edgeSqrt_P a x 0 δ
  set Q := edgeSqrt_Q a x 0 δ
  set S := edgeSqrt_S a x 0 δ
  have hQpos : 0 < Q := by
    have hP0 : 0 < P := by linarith
    have : 0 < τ / 2 * P := by positivity
    linarith
  have hz₀im : 0 < z₀.im := by
    rw [hz₀, him]
    simp only [mul_zero, zero_mul, zero_add]
    positivity
  have hm₀ : mW a z₀ = stieltjesA a w₀ := by
    apply mW_eq_of_spec hN a hz₀im
    · rw [hsim]
      have : 0 < S := by linarith
      positivity
    · rw [hz₀]; ring_nf
  have hFz₀ : F z₀ = w₀ := by
    change z₀ + mW a z₀ = w₀
    rw [hm₀, hz₀]
    ring
  have hz₀H : z₀ ∈ H := by
    refine ⟨hz₀im, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [hL, hre, abs_of_pos hz₀im, him]
    have hP0 : 0 < P := by linarith
    have hQb : δ * Q ≤ P := by
      have : δ * Q ≤ δ * (4 / τ * P) := mul_le_mul_of_nonneg_left hQ2 hδpos.le
      have h2 : δ * (4 / τ * P) ≤ P := by
        rw [hδ]
        have : τ ^ 2 / 512 * (4 / τ * P) = τ / 128 * P := by field_simp; ring
        rw [this]
        have : τ / 128 ≤ 1 := by linarith
        nlinarith
      linarith
    have e1 : |(0 ^ 2 - δ ^ 2) * P + 0 * (0 ^ 2 + δ ^ 2) * Q| = δ ^ 2 * P := by
      rw [show (0 ^ 2 - δ ^ 2) * P + 0 * (0 ^ 2 + δ ^ 2) * Q = -(δ ^ 2 * P) by ring, abs_neg,
        abs_of_pos (by positivity)]
    rw [e1]
    have e2 : δ * (2 * 0 * P + (0 ^ 2 + δ ^ 2) * Q) = δ ^ 2 * (δ * Q) := by ring
    rw [e2]
    have h3 : δ ^ 2 * P + δ ^ 2 * (δ * Q) ≤ δ ^ 2 * (2 * (8 / τ)) := by
      have : δ ^ 2 * (δ * Q) ≤ δ ^ 2 * P := mul_le_mul_of_nonneg_left hQb (by positivity)
      have : δ ^ 2 * P ≤ δ ^ 2 * (8 / τ) := mul_le_mul_of_nonneg_left hP2 (by positivity)
      nlinarith
    have h4 : δ ^ 2 * (2 * (8 / τ)) ≤ τ ^ 3 / 4096 := by
      rw [hδ]
      have : (τ ^ 2 / 512) ^ 2 * (2 * (8 / τ)) = τ ^ 3 / 16384 := by field_simp; ring
      rw [this]
      have : 0 ≤ τ ^ 3 := by positivity
      linarith
    linarith
  have hz₀U : z₀ ∈ U := by
    refine ⟨hz₀im, ?_⟩
    change F z₀ ∈ Metric.ball (x : ℂ) (τ / 16)
    rw [hFz₀, Metric.mem_ball, dist_eq_norm]
    have : w₀ - (x : ℂ) = ⟨0, δ⟩ := Complex.ext (by simp [hw₀]) (by simp [hw₀])
    rw [this]
    have : ‖(⟨0, δ⟩ : ℂ)‖ = δ := by
      rw [show (⟨0, δ⟩ : ℂ) = (δ : ℂ) * Complex.I from Complex.ext (by simp) (by simp),
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
    rw [this]
    rw [abs_of_pos hδpos] at hδb
    have : τ ^ 2 / 512 < τ / 16 := by nlinarith
    linarith
  have hclosed : closure U ∩ H ⊆ U := by
    rintro y ⟨hyc, hyH⟩
    have hyim : 0 < y.im := hyH.1
    have hyc' : ‖y - (LpW a : ℂ)‖ ≤ τ ^ 3 / 4096 := by
      have := hyH.2
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    have hle : ‖F y - x‖ ≤ τ / 16 := by
      by_contra h
      push Not at h
      have hca : ContinuousAt (fun y => ‖F y - x‖) y :=
        ((hcont.continuousAt ((Complex.isOpen_im_gt 0).mem_nhds hyim)).sub
          continuousAt_const).norm
      obtain ⟨y', hy'1, hy'2⟩ := mem_closure_iff_nhds.1 hyc _ (hca.eventually (lt_mem_nhds h))
      have := hy'2.2
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at this
      have h' : τ / 16 < ‖F y' - x‖ := hy'1
      linarith
    exact ⟨hyim, by
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
      exact key y hyim hyc' hle⟩
  have hsub := hpre.subset_of_closure_inter_subset hopen ⟨z₀, hz₀H, hz₀U⟩ hclosed
  have hzH : z ∈ H := ⟨hz, by rwa [Metric.mem_closedBall, dist_eq_norm]⟩
  have := (hsub hzH).2
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at this
  exact this

/-- Square-root behaviour of `Im m^W` at `L₊` (§12.4): within `c` of `L₊`, `Im m^W ≍ √(κ + η)`
for `E ≤ L₊` and `Im m^W ≍ η / √(κ + η)` for `E ≥ L₊`, `κ = |E − L₊|`, with constants depending
only on `τ`. -/
theorem im_mW_sqrt_edge {τ : ℝ} (hτ : 0 < τ) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) →
      ∀ z : ℂ, 0 < z.im → ‖z - (LpW a : ℂ)‖ ≤ c →
        (z.re ≤ LpW a → K⁻¹ * √(LpW a - z.re + z.im) ≤ (mW a z).im ∧
            (mW a z).im ≤ K * √(LpW a - z.re + z.im)) ∧
        (LpW a ≤ z.re → K⁻¹ * (z.im / √(z.re - LpW a + z.im)) ≤ (mW a z).im ∧
            (mW a z).im ≤ K * (z.im / √(z.re - LpW a + z.im))) := by
  obtain ⟨N₁, hN₁⟩ := xpW_sub_ge hτ
  refine ⟨τ ^ 3 / 4096, 18 / τ, by positivity, by positivity, max N₁ 1,
    fun N hN a ha hSB z hz hzc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  by_cases hτ2 : τ ≤ 1 / 2
  swap
  · exfalso
    have h1 := ha ⟨0, hN1⟩
    have h2 : τ⁻¹ < 2 := by rw [inv_lt_comm₀ hτ (by norm_num)]; push Not at hτ2; linarith
    linarith [abs_nonneg (a ⟨0, hN1⟩)]
  have hgap := (hN₁ N (le_of_max_le_left hN) a ha hSB).1
  obtain ⟨he1, he2, hS⟩ := edgeSqrt_xp_facts hN1 hτ ha hgap
  have hw := edgeSqrt_boot hN1 hτ hτ2 he1 he2 hS z hz hzc
  obtain ⟨hm, heq⟩ := mW_spec hN1 a hz
  have hwz : z + mW a z - stieltjesA a (z + mW a z) = z := by rw [← heq]; ring
  have hq : 0 < (z + mW a z).im := by rw [Complex.add_im]; linarith
  have hl := (edgeSqrt_local hτ hτ2 he1 he2 hS (z + mW a z) hw.le hq (by rw [hwz]; exact hz)).2
  rw [hwz, ← heq] at hl
  exact hl

/-- `g(x + t) − g(x) = t² N⁻¹ ∑ᵢ 1/(eᵢ² (eᵢ + t))` with `eᵢ = x − aᵢ`, when `S(x) = 1`. -/
private lemma edgeSqrt_gW_sub {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hS : sW a x = 1)
    (hx : ∀ i, a i < x) {t : ℝ} (ht : 0 ≤ t) :
    gW a (x + t) - gW a x =
      t ^ 2 * ((N : ℝ)⁻¹ * ∑ i, 1 / ((x - a i) ^ 2 * (x - a i + t))) := by
  have hS' : (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹ = 1 := hS
  have hsum : ∑ i, (t * ((a i - x) ^ 2)⁻¹ - (a i - (x + t))⁻¹ + (a i - x)⁻¹) =
      ∑ i, t ^ 2 * (1 / ((x - a i) ^ 2 * (x - a i + t))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : x - a i ≠ 0 := (sub_pos.2 (hx i)).ne'
    have h2 : x - a i + t ≠ 0 := by have := hx i; positivity
    have h3 : a i - (x + t) ≠ 0 := fun h => h2 (by linarith)
    have h4 : a i - x ≠ 0 := fun h => h1 (by linarith)
    field_simp
    ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  unfold gW
  linear_combination (-t) * hS' + (N : ℝ)⁻¹ * hsum

/-- `1 − S(x + t) = N⁻¹ ∑ᵢ (eᵢ⁻² − (eᵢ + t)⁻²)` with `eᵢ = x − aᵢ`, when `S(x) = 1`. -/
private lemma edgeSqrt_one_sub_sW {N : ℕ} (a : Fin N → ℝ) {x : ℝ} (hS : sW a x = 1) (t : ℝ) :
    1 - sW a (x + t) = (N : ℝ)⁻¹ * ∑ i, (((a i - x) ^ 2)⁻¹ - ((a i - (x + t)) ^ 2)⁻¹) := by
  have hS' : (N : ℝ)⁻¹ * ∑ i, ((a i - x) ^ 2)⁻¹ = 1 := hS
  rw [Finset.sum_sub_distrib, mul_sub, hS']
  rfl

/-- `1 − e²/(e + t)² ≥ min(tτ, 1)/4` for `0 < e ≤ 2/τ`, `t ≥ 0`, in the form
`min(tτ, 1)/4 · e⁻² ≤ e⁻² − (e + t)⁻²`. -/
private lemma edgeSqrt_term_d {τ e t : ℝ} (hτ : 0 < τ) (he : 0 < e) (he2 : τ * e ≤ 2)
    (ht : 0 ≤ t) :
    min (t * τ) 1 / 4 * (e ^ 2)⁻¹ ≤ (e ^ 2)⁻¹ - ((e + t) ^ 2)⁻¹ := by
  have hm1 : min (t * τ) 1 ≤ t * τ := min_le_left _ _
  have hm2 : min (t * τ) 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 ≤ min (t * τ) 1 := le_min (by positivity) zero_le_one
  have hkey : min (t * τ) 1 / 4 * (e + t) ^ 2 ≤ t * (2 * e + t) := by
    rcases le_total t e with h | h
    · have h1 : (e + t) ^ 2 ≤ 4 * e ^ 2 := by nlinarith
      have h2 : min (t * τ) 1 / 4 * (e + t) ^ 2 ≤ t * τ / 4 * (4 * e ^ 2) :=
        mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      have h3 : t * τ / 4 * (4 * e ^ 2) = t * e * (τ * e) := by ring
      have h4 : t * e * (τ * e) ≤ t * e * 2 := mul_le_mul_of_nonneg_left he2 (by positivity)
      nlinarith
    · have h1 : (e + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
      have h2 : min (t * τ) 1 / 4 * (e + t) ^ 2 ≤ 1 / 4 * (4 * t ^ 2) :=
        mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
      nlinarith
  have het : 0 < e + t := by linarith
  have e1 : (e ^ 2)⁻¹ - ((e + t) ^ 2)⁻¹ = t * (2 * e + t) / (e ^ 2 * (e + t) ^ 2) := by
    field_simp; ring
  rw [e1, le_div_iff₀ (by positivity)]
  calc min (t * τ) 1 / 4 * (e ^ 2)⁻¹ * (e ^ 2 * (e + t) ^ 2) =
      min (t * τ) 1 / 4 * (e + t) ^ 2 := by field_simp
    _ ≤ t * (2 * e + t) := hkey

/-- Lower bound on `g′(x₀) = 1 − S(x₀)` at `x₀ = x₊ + t`, `t > 0`, against `κ = g(x₀) − L₊`
(§12.4): `(1 − S(x₀))² ≥ τ³ min(κ, 1)/64`, together with `0 < 1 − S(x₀) ≤ 1`. -/
private lemma edgeSqrt_d_bound {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    {a : Fin N → ℝ} {x : ℝ} (he1 : ∀ i, τ / 4 ≤ x - a i) (he2 : ∀ i, x - a i ≤ 2 / τ)
    (hS : sW a x = 1) {t : ℝ} (ht : 0 < t) :
    0 < 1 - sW a (x + t) ∧ 1 - sW a (x + t) ≤ 1 ∧
      τ ^ 3 / 64 * min (gW a (x + t) - gW a x) 1 ≤ (1 - sW a (x + t)) ^ 2 := by
  have hx : ∀ i, a i < x := fun i => by linarith [he1 i]
  have hd : min (t * τ) 1 / 4 ≤ 1 - sW a (x + t) := by
    rw [edgeSqrt_one_sub_sW a hS]
    apply edgeSqrt_avg_ge a hS
    intro i
    have h0 : 0 < x - a i := by linarith [he1 i]
    have h2 : τ * (x - a i) ≤ 2 := by
      have := he2 i; rw [le_div_iff₀ hτ] at this; linarith
    have := edgeSqrt_term_d hτ h0 h2 ht.le
    have r1 : (a i - x) ^ 2 = (x - a i) ^ 2 := by ring
    have r2 : (a i - (x + t)) ^ 2 = (x - a i + t) ^ 2 := by ring
    rw [r1, r2]
    exact this
  have hm0 : 0 < min (t * τ) 1 := lt_min (by positivity) one_pos
  have hsW0 : 0 ≤ sW a (x + t) := by unfold sW; positivity
  refine ⟨by linarith, by linarith, ?_⟩
  have hκ : gW a (x + t) - gW a x ≤ 4 / τ * t ^ 2 := by
    rw [edgeSqrt_gW_sub a hS hx ht.le, mul_comm]
    refine mul_le_mul_of_nonneg_right (edgeSqrt_avg_le a hS _ fun i => ?_) (sq_nonneg t)
    have h0 : 0 < x - a i := by linarith [he1 i]
    have h1 := he1 i
    have r1 : (a i - x) ^ 2 = (x - a i) ^ 2 := by ring
    rw [r1, div_le_iff₀ (by positivity)]
    have : 1 ≤ 4 / τ * (x - a i) := by rw [div_mul_eq_mul_div, le_div_iff₀ hτ]; linarith
    calc (1 : ℝ) ≤ 4 / τ * (x - a i) := this
      _ ≤ 4 / τ * (x - a i + t) := by gcongr; linarith
      _ = 4 / τ * ((x - a i) ^ 2)⁻¹ * ((x - a i) ^ 2 * (x - a i + t)) := by field_simp
  set κ := gW a (x + t) - gW a x
  have hd2 : (min (t * τ) 1 / 4) ^ 2 ≤ (1 - sW a (x + t)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  have hτ3 : τ ^ 3 ≤ 1 := by
    calc τ ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hτ.le hτ2 3
      _ ≤ 1 := by norm_num
  have hmk : τ ^ 3 / 4 * min κ 1 ≤ min (t * τ) 1 ^ 2 := by
    rcases le_total (t * τ) 1 with h | h
    · rw [min_eq_left h]
      have : τ ^ 3 / 4 * min κ 1 ≤ τ ^ 3 / 4 * κ :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      have h2 : τ ^ 3 / 4 * κ ≤ τ ^ 3 / 4 * (4 / τ * t ^ 2) :=
        mul_le_mul_of_nonneg_left hκ (by positivity)
      have h3 : τ ^ 3 / 4 * (4 / τ * t ^ 2) = (t * τ) ^ 2 := by field_simp
      linarith
    · rw [min_eq_right h]
      have : τ ^ 3 / 4 * min κ 1 ≤ τ ^ 3 / 4 * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      nlinarith
  nlinarith

/-- Complex conjugation commutes with `m_A`. -/
private lemma edgeSqrt_stieltjesA_conj {N : ℕ} (a : Fin N → ℝ) (w : ℂ) :
    stieltjesA a ((starRingEnd ℂ) w) = (starRingEnd ℂ) (stieltjesA a w) := by
  unfold stieltjesA
  rw [map_mul, map_inv₀, map_sum, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_inv₀, map_sub, Complex.conj_ofReal]

/-- `m_A` at a real point. -/
private lemma edgeSqrt_stieltjesA_ofReal {N : ℕ} (a : Fin N → ℝ) (y : ℝ) :
    stieltjesA a (y : ℂ) = (((N : ℝ)⁻¹ * ∑ i, (a i - y)⁻¹ : ℝ) : ℂ) := by
  unfold stieltjesA; push_cast; rfl

/-- `|A⁻² − ((A − u)(A − u′))⁻¹| ≤ 12ρ/|A|³` for real `A ≠ 0` and `|u|, |u′| ≤ ρ ≤ |A|/2`. -/
private lemma edgeSqrt_term_approx {A ρ : ℝ} {u u' : ℂ} (hA : 0 < |A|) (hρ : ρ ≤ |A| / 2)
    (hu : ‖u‖ ≤ ρ) (hu' : ‖u'‖ ≤ ρ) :
    ‖((A : ℂ) ^ 2)⁻¹ - (((A : ℂ) - u) * ((A : ℂ) - u'))⁻¹‖ ≤ 12 * ρ / |A| ^ 3 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg u).trans hu
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.1 hA)
  have hn1 : |A| / 2 ≤ ‖(A : ℂ) - u‖ := by
    have := norm_sub_norm_le (A : ℂ) u
    rw [Complex.norm_real, Real.norm_eq_abs] at this; linarith
  have hn2 : |A| / 2 ≤ ‖(A : ℂ) - u'‖ := by
    have := norm_sub_norm_le (A : ℂ) u'
    rw [Complex.norm_real, Real.norm_eq_abs] at this; linarith
  have h1 : (A : ℂ) - u ≠ 0 := fun h => by rw [h, norm_zero] at hn1; linarith
  have h2 : (A : ℂ) - u' ≠ 0 := fun h => by rw [h, norm_zero] at hn2; linarith
  have e : ((A : ℂ) ^ 2)⁻¹ - (((A : ℂ) - u) * ((A : ℂ) - u'))⁻¹ =
      (u * u' - A * (u + u')) / ((A : ℂ) ^ 2 * (((A : ℂ) - u) * ((A : ℂ) - u'))) := by
    field_simp; ring
  have hnum : ‖u * u' - A * (u + u')‖ ≤ 3 * |A| * ρ := by
    calc ‖u * u' - A * (u + u')‖ ≤ ‖u * u'‖ + ‖(A : ℂ) * (u + u')‖ := norm_sub_le _ _
      _ ≤ ρ * ρ + |A| * (ρ + ρ) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hu hu')
      _ ≤ 3 * |A| * ρ := by nlinarith
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hden : |A| ^ 2 * (|A| / 2 * (|A| / 2)) ≤
      |A| ^ 2 * (‖(A : ℂ) - u‖ * ‖(A : ℂ) - u'‖) := by gcongr
  calc ‖u * u' - A * (u + u')‖ * |A| ^ 3 ≤ 3 * |A| * ρ * |A| ^ 3 := by gcongr
    _ = 12 * ρ * (|A| ^ 2 * (|A| / 2 * (|A| / 2))) := by ring
    _ ≤ 12 * ρ * (|A| ^ 2 * (‖(A : ℂ) - u‖ * ‖(A : ℂ) - u'‖)) := by gcongr

/-- `|N⁻¹ ∑ᵢ ((aᵢ − x₀)⁻² − ((aᵢ − w)(aᵢ − w′))⁻¹)| ≤ 48ρ/τ` for `|w − x₀|, |w′ − x₀| ≤ ρ ≤ τ/8`,
`x₀ − aᵢ ≥ τ/4` and `S(x₀) ≤ 1`. -/
private lemma edgeSqrt_bracket {N : ℕ} (a : Fin N → ℝ) {τ x₀ ρ : ℝ} (hτ : 0 < τ)
    (hf : ∀ i, τ / 4 ≤ x₀ - a i) (hS : sW a x₀ ≤ 1) (hρ : ρ ≤ τ / 8) {w w' : ℂ}
    (hw : ‖w - x₀‖ ≤ ρ) (hw' : ‖w' - x₀‖ ≤ ρ) :
    ‖(N : ℂ)⁻¹ * ∑ i, ((((a i - x₀ : ℝ) : ℂ) ^ 2)⁻¹ - (((a i : ℂ) - w) * ((a i : ℂ) - w'))⁻¹)‖ ≤
      48 * ρ / τ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hw
  have hA : ∀ i, 0 < |a i - x₀| ∧ τ / 4 ≤ |a i - x₀| := fun i => by
    have h := hf i
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    exact ⟨by linarith, h⟩
  have hu : ∀ i, (((a i - x₀ : ℝ) : ℂ) - (w - x₀)) = (a i : ℂ) - w := fun i => by push_cast; ring
  have hu' : ∀ i, (((a i - x₀ : ℝ) : ℂ) - (w' - x₀)) = (a i : ℂ) - w' := fun i => by
    push_cast; ring
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, ((((a i - x₀ : ℝ) : ℂ) ^ 2)⁻¹ - (((a i : ℂ) - w) * ((a i : ℂ) - w'))⁻¹)‖
      ≤ (N : ℝ)⁻¹ * ∑ i, 48 * ρ / τ * ((a i - x₀) ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun i _ => ?_)) (by positivity)
        obtain ⟨h0, h1⟩ := hA i
        have := edgeSqrt_term_approx h0 (by linarith) hw hw'
        rw [hu, hu'] at this
        refine this.trans ?_
        rw [← sq_abs (a i - x₀), div_le_iff₀ (by positivity)]
        have : 4 / τ * |a i - x₀| ≥ 1 := by
          rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hτ]; linarith
        calc 12 * ρ = 12 * ρ * 1 := by ring
          _ ≤ 12 * ρ * (4 / τ * |a i - x₀|) := by gcongr
          _ = 48 * ρ / τ * (|a i - x₀| ^ 2)⁻¹ * |a i - x₀| ^ 3 := by field_simp; ring
    _ = 48 * ρ / τ * sW a x₀ := by
        rw [← Finset.mul_sum, sW]
        ring
    _ ≤ 48 * ρ / τ := by
        have : 0 ≤ 48 * ρ / τ := by positivity
        nlinarith

/-- `g` approximates `g′(x₀) = 1 − S(x₀)` on the disc of radius `ρ ≤ τ/8` about a real `x₀` with
`x₀ − aᵢ ≥ τ/4` and `S(x₀) ≤ 1`: `|g(w) − g(w′) − g′(x₀)(w − w′)| ≤ (48ρ/τ)|w − w′|`. -/
private lemma edgeSqrt_approx {N : ℕ} (a : Fin N → ℝ) {τ x₀ ρ : ℝ} (hτ : 0 < τ)
    (hf : ∀ i, τ / 4 ≤ x₀ - a i) (hS : sW a x₀ ≤ 1) (hρ : ρ ≤ τ / 8) {w w' : ℂ}
    (hw : ‖w - x₀‖ ≤ ρ) (hw' : ‖w' - x₀‖ ≤ ρ) :
    ‖(w - stieltjesA a w) - (w' - stieltjesA a w') - ((1 - sW a x₀ : ℝ) : ℂ) * (w - w')‖ ≤
      48 * ρ / τ * ‖w - w'‖ := by
  have hne : ∀ i, (a i : ℂ) - w ≠ 0 ∧ (a i : ℂ) - w' ≠ 0 := fun i => by
    have h := hf i
    have e1 := norm_sub_norm_le ((a i - x₀ : ℝ) : ℂ) (w - x₀)
    have e2 := norm_sub_norm_le ((a i - x₀ : ℝ) : ℂ) (w' - x₀)
    have r1 : (((a i - x₀ : ℝ) : ℂ) - (w - x₀)) = (a i : ℂ) - w := by push_cast; ring
    have r2 : (((a i - x₀ : ℝ) : ℂ) - (w' - x₀)) = (a i : ℂ) - w' := by push_cast; ring
    rw [r1, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_pos (by linarith)] at e1
    rw [r2, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_pos (by linarith)] at e2
    constructor
    · intro h0; rw [h0, norm_zero] at e1; linarith
    · intro h0; rw [h0, norm_zero] at e2; linarith
  have heq : (w - stieltjesA a w) - (w' - stieltjesA a w') - ((1 - sW a x₀ : ℝ) : ℂ) * (w - w') =
      (w - w') * ((N : ℂ)⁻¹ * ∑ i, ((((a i - x₀ : ℝ) : ℂ) ^ 2)⁻¹ -
        (((a i : ℂ) - w) * ((a i : ℂ) - w'))⁻¹)) := by
    have hterm : ∀ i, ((a i : ℂ) - w)⁻¹ - ((a i : ℂ) - w')⁻¹ =
        (w - w') * (((a i : ℂ) - w) * ((a i : ℂ) - w'))⁻¹ := fun i => by
      obtain ⟨h1, h2⟩ := hne i
      field_simp; ring
    unfold stieltjesA sW
    push_cast
    have hs : ∑ i, ((a i : ℂ) - w)⁻¹ - ∑ i, ((a i : ℂ) - w')⁻¹ =
        (w - w') * ∑ i, (((a i : ℂ) - w) * ((a i : ℂ) - w'))⁻¹ := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hterm i
    rw [Finset.sum_sub_distrib]
    linear_combination (-(N : ℂ)⁻¹) * hs
  rw [heq, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (edgeSqrt_bracket a hτ hf hS hρ hw hw') (norm_nonneg _)

/-- `m_A` is holomorphic away from the spectrum, with `m_A′(w) = N⁻¹ ∑ᵢ (aᵢ − w)⁻²`. -/
private lemma edgeSqrt_hasDerivAt_stieltjesA {N : ℕ} (a : Fin N → ℝ) {w : ℂ}
    (hw : ∀ i, (a i : ℂ) - w ≠ 0) :
    HasDerivAt (stieltjesA a) ((N : ℂ)⁻¹ * ∑ i, (((a i : ℂ) - w) ^ 2)⁻¹) w := by
  unfold stieltjesA
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  have := ((hasDerivAt_id w).const_sub (a i : ℂ)).inv (hw i)
  convert this using 1
  · ext y
    simp
  · simp

/-- Local inverse of `g(w) = w − m_A(w)` about a real point `x₀` with `x₀ − aᵢ ≥ τ/4` and
`d = 1 − S(x₀) > 0` (§12.4): with `ρ = dτ/96` there is `G`, holomorphic on the disc of radius
`dρ/4` about `E = g(x₀)`, with `|G − x₀| < ρ`, `g ∘ G = id`, `G(ζ̄) = conj G(ζ)` and `Im G > 0` on
the upper half-disc. -/
private lemma edgeSqrt_inverse {N : ℕ} (a : Fin N → ℝ) {τ x₀ E : ℝ} (hτ : 0 < τ)
    (hf : ∀ i, τ / 4 ≤ x₀ - a i) (hd0 : 0 < 1 - sW a x₀) (hE : gW a x₀ = E) :
    ∃ G : ℂ → ℂ, ∀ ζ ∈ Metric.ball (E : ℂ) ((1 - sW a x₀) * ((1 - sW a x₀) * τ / 96) / 4),
      ‖G ζ - x₀‖ < (1 - sW a x₀) * τ / 96 ∧ G ζ - stieltjesA a (G ζ) = ζ ∧
      DifferentiableAt ℂ G ζ ∧ G ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (G ζ) ∧
      (0 < ζ.im → 0 < (G ζ).im) := by
  set d := 1 - sW a x₀ with hd
  set ρ := d * τ / 96 with hρ
  have hsW0 : 0 ≤ sW a x₀ := by unfold sW; positivity
  have hd1 : d ≤ 1 := by linarith
  have hρ0 : 0 < ρ := by positivity
  have hρ8 : ρ ≤ τ / 8 := by
    have : d * τ ≤ 1 * τ := mul_le_mul_of_nonneg_right hd1 hτ.le
    rw [hρ]; linarith
  have hS1 : sW a x₀ ≤ 1 := by linarith
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have h48 : 48 * ρ / τ = d / 2 := by rw [hρ]; field_simp; ring
  set h : ℂ → ℂ := fun w => (x₀ : ℂ) + (w - stieltjesA a w - E) / d with hh
  have happ : ∀ w ∈ Metric.ball (x₀ : ℂ) ρ, ∀ w' ∈ Metric.ball (x₀ : ℂ) ρ,
      ‖h w - h w' - (w - w')‖ ≤ 1 / 2 * ‖w - w'‖ := by
    intro w hw w' hw'
    have e : h w - h w' - (w - w') =
        ((w - stieltjesA a w) - (w' - stieltjesA a w') - (d : ℂ) * (w - w')) / d := by
      simp only [hh]; field_simp; ring
    rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, div_le_iff₀ hd0]
    have := edgeSqrt_approx a hτ hf hS1 hρ8 (mem_ball_iff_norm.1 hw).le
      (mem_ball_iff_norm.1 hw').le
    rw [h48] at this
    calc _ ≤ d / 2 * ‖w - w'‖ := this
      _ = 1 / 2 * ‖w - w'‖ * d := by ring
  have hA : ApproximatesLinearOn h ((ContinuousLinearEquiv.refl ℂ ℂ : ℂ ≃L[ℂ] ℂ) : ℂ →L[ℂ] ℂ)
      (Metric.ball (x₀ : ℂ) ρ) (1 / 2) := by
    intro w hw w' hw'
    simpa using happ w hw w' hw'
  have hc : Subsingleton ℂ ∨
      (1 / 2 : ℝ≥0) < ‖((ContinuousLinearEquiv.refl ℂ ℂ).symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
    right; simp; norm_num
  set Φ := hA.toOpenPartialHomeomorph h (Metric.ball (x₀ : ℂ) ρ) hc Metric.isOpen_ball with hΦ
  have hsrc : Φ.source = Metric.ball (x₀ : ℂ) ρ := rfl
  have hcoe : (Φ : ℂ → ℂ) = h := rfl
  have hhx : h x₀ = x₀ := by
    simp only [hh]
    rw [edgeSqrt_stieltjesA_ofReal, ← hE]
    unfold gW
    push_cast
    ring
  have htgt : Metric.closedBall (x₀ : ℂ) (ρ / 4) ⊆ Φ.target := by
    have := hA.closedBall_subset_target hc Metric.isOpen_ball (b := (x₀ : ℂ)) (ε := ρ / 2)
      (by positivity) (Metric.closedBall_subset_ball (by linarith))
    convert this using 2
    · exact hhx.symm
    · simp; ring
  have hconj_h : ∀ w, h ((starRingEnd ℂ) w) = (starRingEnd ℂ) (h w) := fun w => by
    simp only [hh]
    rw [edgeSqrt_stieltjesA_conj, map_add, map_div₀, map_sub, map_sub, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_ofReal]
  have hyT : ∀ ζ ∈ Metric.ball (E : ℂ) (d * ρ / 4), (x₀ : ℂ) + (ζ - E) / d ∈ Φ.target := by
    intro ζ hζ
    apply htgt
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hd0, div_le_iff₀ hd0]
    have := (mem_ball_iff_norm.1 hζ).le
    linarith
  have hgG : ∀ ζ ∈ Metric.ball (E : ℂ) (d * ρ / 4),
      Φ.symm ((x₀ : ℂ) + (ζ - E) / d) - stieltjesA a (Φ.symm ((x₀ : ℂ) + (ζ - E) / d)) = ζ := by
    intro ζ hζ
    have h1 := Φ.right_inv (hyT ζ hζ)
    rw [hcoe] at h1
    simp only [hh, add_right_inj] at h1
    have := (div_left_inj' hdC).1 h1
    linear_combination this
  have hconj_ball : ∀ ζ ∈ Metric.ball (E : ℂ) (d * ρ / 4),
      (starRingEnd ℂ) ζ ∈ Metric.ball (E : ℂ) (d * ρ / 4) := by
    intro ζ hζ
    rw [mem_ball_iff_norm] at hζ ⊢
    rwa [show (starRingEnd ℂ) ζ - E = (starRingEnd ℂ) (ζ - E) by
      rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]
  have hconj_src : ∀ w ∈ Metric.ball (x₀ : ℂ) ρ, (starRingEnd ℂ) w ∈ Metric.ball (x₀ : ℂ) ρ := by
    intro w hw
    rw [mem_ball_iff_norm] at hw ⊢
    rwa [show (starRingEnd ℂ) w - x₀ = (starRingEnd ℂ) (w - x₀) by
      rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]
  refine ⟨fun ζ => Φ.symm ((x₀ : ℂ) + (ζ - E) / d), fun ζ hζ => ?_⟩
  have hy := hyT ζ hζ
  set y := (x₀ : ℂ) + (ζ - E) / d with hydef
  set w := Φ.symm y with hwdef
  have hws : w ∈ Metric.ball (x₀ : ℂ) ρ := Φ.map_target hy
  have hwy : h w = y := by rw [← hcoe]; exact Φ.right_inv hy
  refine ⟨mem_ball_iff_norm.1 hws, hgG ζ hζ, ?_, ?_, ?_⟩
  · have hwne : ∀ i, (a i : ℂ) - w ≠ 0 := fun i => by
      have h1 := hf i
      have e1 := norm_sub_norm_le ((a i - x₀ : ℝ) : ℂ) (w - x₀)
      have r1 : (((a i - x₀ : ℝ) : ℂ) - (w - x₀)) = (a i : ℂ) - w := by push_cast; ring
      rw [r1, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_pos (by linarith)] at e1
      have := mem_ball_iff_norm.1 hws
      intro h0; rw [h0, norm_zero] at e1; linarith
    set D := (1 - (N : ℂ)⁻¹ * ∑ i, (((a i : ℂ) - w) ^ 2)⁻¹) / d with hD
    have hder : HasDerivAt h D w := by
      have := (((hasDerivAt_id w).sub (edgeSqrt_hasDerivAt_stieltjesA a hwne)).sub_const
        (E : ℂ)).div_const (d : ℂ) |>.const_add (x₀ : ℂ)
      convert this using 1
      funext v
      simp only [hh, Pi.sub_apply, id]
    have hD0 : D ≠ 0 := by
      have hb := edgeSqrt_bracket a hτ hf hS1 hρ8 (mem_ball_iff_norm.1 hws).le
        (mem_ball_iff_norm.1 hws).le
      rw [h48] at hb
      have e : D - 1 = ((N : ℂ)⁻¹ * ∑ i, ((((a i - x₀ : ℝ) : ℂ) ^ 2)⁻¹ -
          (((a i : ℂ) - w) * ((a i : ℂ) - w))⁻¹)) / d := by
        have hdc : (d : ℂ) = 1 - (N : ℂ)⁻¹ * ∑ i, (((a i - x₀ : ℝ) : ℂ) ^ 2)⁻¹ := by
          rw [hd]; unfold sW; push_cast; ring
        rw [hD, eq_div_iff hdC, sub_mul, div_mul_cancel₀ _ hdC, one_mul]
        rw [hdc]
        rw [Finset.sum_sub_distrib]
        simp only [sq]
        ring
      have hn : ‖D - 1‖ ≤ 1 / 2 := by
        rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, div_le_iff₀ hd0]
        linarith
      intro h0
      rw [h0, zero_sub, norm_neg, norm_one] at hn
      norm_num at hn
    have hsymm := Φ.hasDerivAt_symm hy hD0 (by rw [hcoe]; exact hder)
    have haff : HasDerivAt (fun ζ : ℂ => (x₀ : ℂ) + (ζ - E) / d) (1 / d) ζ := by
      have := ((hasDerivAt_id ζ).sub_const (E : ℂ)).div_const (d : ℂ) |>.const_add (x₀ : ℂ)
      simpa using this
    exact (hsymm.comp ζ haff).differentiableAt
  · have hζ' := hconj_ball ζ hζ
    have hy' := hyT _ hζ'
    have hw' : Φ.symm ((x₀ : ℂ) + ((starRingEnd ℂ) ζ - E) / d) ∈ Metric.ball (x₀ : ℂ) ρ :=
      Φ.map_target hy'
    have h1 : h (Φ.symm ((x₀ : ℂ) + ((starRingEnd ℂ) ζ - E) / d)) =
        (x₀ : ℂ) + ((starRingEnd ℂ) ζ - E) / d := by rw [← hcoe]; exact Φ.right_inv hy'
    have h2 : h ((starRingEnd ℂ) w) = (x₀ : ℂ) + ((starRingEnd ℂ) ζ - E) / d := by
      rw [hconj_h, hwy, hydef, map_add, map_div₀, map_sub, Complex.conj_ofReal,
        Complex.conj_ofReal, Complex.conj_ofReal]
    have := Φ.injOn (hconj_src w hws) hw' (by rw [hcoe, h1, h2])
    exact this.symm
  · intro hζim
    by_contra hle
    push Not at hle
    have hb := happ w hws _ (hconj_src w hws)
    rw [hconj_h, hwy, Complex.sub_conj, Complex.sub_conj] at hb
    have him := (Complex.abs_im_le_norm _).trans hb
    have e1 : (((2 * y.im : ℝ) : ℂ) * Complex.I - ((2 * w.im : ℝ) : ℂ) * Complex.I).im =
        2 * y.im - 2 * w.im := by simp
    have e2 : ‖((2 * w.im : ℝ) : ℂ) * Complex.I‖ = 2 * (-w.im) := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    have e3 : y.im = ζ.im / d := by
      rw [hydef]
      simp [Complex.div_ofReal_im]
    rw [e1, e2] at him
    have : 0 < ζ.im / d := div_pos hζim hd0
    have := le_abs_self (2 * y.im - 2 * w.im)
    linarith

/-- `Im m_A(w) > 0` for `Im w > 0` and `N ≥ 1`. -/
private lemma edgeSqrt_im_stieltjesA_pos {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {w : ℂ}
    (hw : 0 < w.im) : 0 < (stieltjesA a w).im := by
  rw [(edgeSqrt_stieltjesA_re_im a w).2]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (inv_pos.2 hNpos)
    (Finset.sum_pos (fun i _ => by positivity) Finset.univ_nonempty)

/-- `g` is continuous to the right of the spectrum. -/
private lemma edgeSqrt_gW_continuousOn {N : ℕ} (a : Fin N → ℝ) {s : Set ℝ}
    (hs : ∀ y ∈ s, ∀ i, a i < y) : ContinuousOn (gW a) s := by
  unfold gW
  refine continuousOn_id.sub (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => ?_))
  exact (continuousOn_const.sub continuousOn_id).inv₀ fun y hy => (sub_neg.2 (hs y hy i)).ne

/-- `y ≤ g(y)` to the right of the spectrum. -/
private lemma edgeSqrt_le_gW {N : ℕ} (a : Fin N → ℝ) {y : ℝ} (hy : ∀ i, a i < y) :
    y ≤ gW a y := by
  unfold gW
  have : (N : ℝ)⁻¹ * ∑ i, (a i - y)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Finset.sum_nonpos fun i _ => (inv_neg''.2 (sub_neg.2 (hy i))).le)
  linarith

/-- Analytic continuation of `m^W` across the real axis to the right of `L₊` (§12.4): on the disc
of radius `c · min(E − L₊, 1)` about `E > L₊` there is an analytic `f` equal to `m^W` on the upper
half-disc, with `f(ζ̄) = conj f(ζ)` and `|f| ≤ K`. -/
theorem mW_continuation_right {τ : ℝ} (hτ : 0 < τ) :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) → ∀ E : ℝ, LpW a < E →
        ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball (E : ℂ) (c * min (E - LpW a) 1)) ∧
          (∀ ζ ∈ Metric.ball (E : ℂ) (c * min (E - LpW a) 1), 0 < ζ.im → f ζ = mW a ζ) ∧
          (∀ ζ ∈ Metric.ball (E : ℂ) (c * min (E - LpW a) 1),
            f ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (f ζ)) ∧
          (∀ ζ ∈ Metric.ball (E : ℂ) (c * min (E - LpW a) 1), ‖f ζ‖ ≤ K) := by
  obtain ⟨N₁, hN₁⟩ := xpW_sub_ge hτ
  refine ⟨min (τ ^ 4 / 32768) (1 / 4), 2 + 4 / τ, lt_min (by positivity) (by norm_num),
    min_le_right _ _, by positivity, max N₁ 1, fun N hN a ha hSB E hE => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  by_cases hτ2 : τ ≤ 1 / 2
  swap
  · exfalso
    have h1 := ha ⟨0, hN1⟩
    have h2 : τ⁻¹ < 2 := by rw [inv_lt_comm₀ hτ (by norm_num)]; push Not at hτ2; linarith
    linarith [abs_nonneg (a ⟨0, hN1⟩)]
  have hgap := (hN₁ N (le_of_max_le_left hN) a ha hSB).1
  obtain ⟨he1, he2, hS⟩ := edgeSqrt_xp_facts hN1 hτ ha hgap
  set x := xpW a with hxdef
  have hL : LpW a = gW a x := rfl
  have hx : ∀ i, a i < x := fun i => by linarith [he1 i]
  -- the point `x₀ > x₊` with `g(x₀) = E`
  have hxL : x ≤ LpW a := hL ▸ edgeSqrt_le_gW a hx
  have hxE : x ≤ E := by linarith
  have hcont : ContinuousOn (gW a) (Set.Icc x E) :=
    edgeSqrt_gW_continuousOn a fun y hy i => lt_of_lt_of_le (hx i) hy.1
  have hEg : E ≤ gW a E := edgeSqrt_le_gW a fun i => lt_of_lt_of_le (hx i) hxE
  obtain ⟨x₀, ⟨hx₀1, hx₀2⟩, hgx₀⟩ :=
    intermediate_value_Icc hxE hcont ⟨by rw [← hL]; exact hE.le, hEg⟩
  have hx₀ : x < x₀ := by
    rcases eq_or_lt_of_le hx₀1 with h | h
    · rw [← h, ← hL] at hgx₀; linarith
    · exact h
  set t := x₀ - x with ht
  have htpos : 0 < t := by linarith
  have hx₀t : x₀ = x + t := by ring
  obtain ⟨hd0, hd1, hd2⟩ := edgeSqrt_d_bound hN1 hτ hτ2 he1 he2 hS htpos
  simp only [← hx₀t] at hd0 hd1 hd2
  rw [hgx₀, ← hL] at hd2
  set d := 1 - sW a x₀ with hd
  have hf : ∀ i, τ / 4 ≤ x₀ - a i := fun i => by linarith [he1 i]
  obtain ⟨G, hG⟩ := edgeSqrt_inverse a hτ hf hd0 hgx₀
  set m := min (E - LpW a) 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  set c := min (τ ^ 4 / 32768) (1 / 4) with hc
  have hrad : c * m ≤ d * (d * τ / 96) / 4 := by
    have h1 : c * m ≤ τ ^ 4 / 32768 * m := mul_le_mul_of_nonneg_right (min_le_left _ _) hm0.le
    have h2 : τ / 384 * (τ ^ 3 / 64 * m) ≤ τ / 384 * d ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 (by positivity)
    have h3 : τ ^ 4 / 32768 * m ≤ τ / 384 * (τ ^ 3 / 64 * m) := by
      have : τ / 384 * (τ ^ 3 / 64 * m) = τ ^ 4 / 24576 * m := by ring
      rw [this]
      gcongr
      norm_num
    have : d * (d * τ / 96) / 4 = τ / 384 * d ^ 2 := by ring
    linarith
  have hsub : Metric.ball (E : ℂ) (c * m) ⊆ Metric.ball (E : ℂ) (d * (d * τ / 96) / 4) :=
    Metric.ball_subset_ball hrad
  refine ⟨fun ζ => G ζ - ζ, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    exact ((hG ζ (hsub hζ)).2.2.1.sub differentiableAt_id).differentiableWithinAt
  · intro ζ hζ hζim
    obtain ⟨-, hgG, -, -, hpos⟩ := hG ζ (hsub hζ)
    have hGim := hpos hζim
    symm
    apply mW_eq_of_spec hN1 a hζim
    · have : G ζ - ζ = stieltjesA a (G ζ) := by linear_combination hgG
      change 0 < (G ζ - ζ).im
      rw [this]
      exact edgeSqrt_im_stieltjesA_pos hN1 a hGim
    · rw [show ζ + (G ζ - ζ) = G ζ by ring]
      linear_combination hgG
  · intro ζ hζ
    obtain ⟨-, -, -, hconj, -⟩ := hG ζ (hsub hζ)
    simp only [hconj, map_sub]
  · intro ζ hζ
    obtain ⟨hGx, -, -, -, -⟩ := hG ζ (hsub hζ)
    have hζE : ‖ζ - E‖ < d * (d * τ / 96) / 4 := mem_ball_iff_norm.1 (hsub hζ)
    have hr1 : d * (d * τ / 96) / 4 ≤ 1 := by
      have : d * (d * τ / 96) ≤ 1 * (1 * (1 / 2) / 96) := by
        apply mul_le_mul hd1 _ (by positivity) (by norm_num)
        have : d * τ ≤ 1 * (1 / 2) := mul_le_mul hd1 hτ2 hτ.le (by norm_num)
        linarith
      linarith
    have hρ1 : d * τ / 96 ≤ 1 := by
      have : d * τ ≤ 1 * (1 / 2) := mul_le_mul hd1 hτ2 hτ.le (by norm_num)
      linarith
    have hx₀E : ‖(x₀ : ℂ) - E‖ ≤ 4 / τ := by
      rw [← hgx₀, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      unfold gW
      have hpos : ∀ i, 0 < x₀ - a i := fun i => by linarith [hf i]
      have e : x₀ - (x₀ - (N : ℝ)⁻¹ * ∑ i, (a i - x₀)⁻¹) = -((N : ℝ)⁻¹ * ∑ i, (x₀ - a i)⁻¹) := by
        have : ∀ i, (a i - x₀)⁻¹ = -(x₀ - a i)⁻¹ := fun i => by rw [← inv_neg, neg_sub]
        simp only [this, Finset.sum_neg_distrib]
        ring
      rw [e, abs_neg, abs_of_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => (inv_pos.2 (hpos i)).le))]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      calc (N : ℝ)⁻¹ * ∑ i, (x₀ - a i)⁻¹ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, 4 / τ := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
            rw [inv_le_comm₀ (hpos i) (by positivity), inv_div]
            exact hf i
        _ = 4 / τ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    calc ‖G ζ - ζ‖ = ‖(G ζ - x₀) + ((x₀ : ℂ) - E) - (ζ - E)‖ := by ring_nf
      _ ≤ ‖G ζ - x₀‖ + ‖(x₀ : ℂ) - E‖ + ‖ζ - E‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 1 + 4 / τ + 1 := by gcongr <;> linarith
      _ = 2 + 4 / τ := by ring

/-- `∏_{j ∈ [1, m+1+r], j ≠ m+1} (j − (m+1)) = (−1)^m m! r!` in `ℂ`. -/
private lemma edgeSqrt_prod_erase (m r : ℕ) :
    ∏ j ∈ (Finset.Icc 1 (m + 1 + r)).erase (m + 1), ((j : ℂ) - ((m + 1 : ℕ) : ℂ)) =
      (-1) ^ m * (Nat.factorial m : ℂ) * (Nat.factorial r : ℂ) := by
  induction r with
  | zero =>
    have h1 : (Finset.Icc 1 (m + 1 + 0)).erase (m + 1) = Finset.Icc 1 m := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.add_sub_cancel]
    have h2 : ∀ j ∈ Finset.range m, ((1 + j : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ) =
        -1 * (((m - 1 - j : ℕ) : ℂ) + 1) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have : ((m - 1 - j : ℕ) : ℂ) = (m : ℂ) - 1 - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp
      rw [this]
      push_cast
      ring
    rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    rw [Finset.prod_range_reflect (fun j : ℕ => ((j : ℂ) + 1)) m]
    have : ∏ j ∈ Finset.range m, ((j : ℂ) + 1) = (Nat.factorial m : ℂ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      rfl
    rw [this]
  | succ r ih =>
    have h1 : (Finset.Icc 1 (m + 1 + (r + 1))).erase (m + 1) =
        insert (m + 1 + (r + 1)) ((Finset.Icc 1 (m + 1 + r)).erase (m + 1)) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h1, Finset.prod_insert (by simp), ih, Nat.factorial_succ]
    push_cast
    ring

/-- Partial fractions in `ℂ` (the identity behind (tur1)): for `c > 0` and `y + kc ≠ 0`,
`∏ₖ (y + kc)⁻¹ = ∑ₖ (c^{n−1} (−1)^{k−1} (k−1)! (n−k)!)⁻¹ (y + kc)⁻¹`, `k ∈ [1, n]`. -/
private lemma edgeSqrt_pf {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) {y : ℂ}
    (hy : ∀ k ∈ Finset.Icc 1 n, y + (k : ℂ) * c ≠ 0) :
    ∏ k ∈ Finset.Icc 1 n, (y + (k : ℂ) * c)⁻¹ =
      ∑ k ∈ Finset.Icc 1 n,
        (((c : ℂ) ^ (n - 1) * ((-1) ^ (k - 1) * (Nat.factorial (k - 1) : ℂ) *
          (Nat.factorial (n - k) : ℂ))))⁻¹ * (y + (k : ℂ) * c)⁻¹ := by
  have hs : (Finset.Icc 1 n).Nonempty := Finset.nonempty_Icc.2 hn
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hinj : Set.InjOn (fun k : ℕ => -((k : ℂ) * c)) (Finset.Icc 1 n : Set ℕ) := by
    intro a _ b _ h
    have : (a : ℂ) * c = b * c := by simpa using h
    exact_mod_cast mul_right_cancel₀ hc' this
  have h := congrArg (Polynomial.eval y) (Lagrange.sum_basis hinj hs)
  simp only [Polynomial.eval_finsetSum, Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one] at h
  have hP : ∏ k ∈ Finset.Icc 1 n, (y + (k : ℂ) * c) ≠ 0 := Finset.prod_ne_zero_iff.2 hy
  rw [Finset.prod_inv_distrib]
  refine mul_right_cancel₀ hP ?_
  rw [inv_mul_cancel₀ hP, Finset.sum_mul]
  refine Eq.trans h.symm (Finset.sum_congr rfl ?_)
  intro k hk
  have hkn := Finset.mem_Icc.1 hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, n = m + 1 + r := ⟨n - (m + 1), by omega⟩
  have hQ : (y + ((m + 1 : ℕ) : ℂ) * c) * ∏ j ∈ (Finset.Icc 1 n).erase (m + 1), (y + (j : ℂ) * c)
      = ∏ j ∈ Finset.Icc 1 n, (y + (j : ℂ) * c) :=
    Finset.mul_prod_erase _ (fun j : ℕ => y + (j : ℂ) * c) hk
  have hk0 : y + ((m + 1 : ℕ) : ℂ) * c ≠ 0 := hy _ hk
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hQ]
  have hD : ∏ j ∈ (Finset.Icc 1 n).erase (m + 1),
      (-(((m + 1 : ℕ) : ℂ) * c) - -((j : ℂ) * c)) =
      (c : ℂ) ^ (n - 1) * ((-1) ^ m * (Nat.factorial m : ℂ) *
        (Nat.factorial (n - (m + 1)) : ℂ)) := by
    have : ∀ j ∈ (Finset.Icc 1 n).erase (m + 1),
        (-(((m + 1 : ℕ) : ℂ) * c) - -((j : ℂ) * c)) = ((j : ℂ) - ((m + 1 : ℕ) : ℂ)) * c :=
      fun j _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem hk, Nat.card_Icc, Nat.add_sub_cancel, hr, edgeSqrt_prod_erase m r]
    have : m + 1 + r - (m + 1) = r := by omega
    rw [this, mul_comm]
  have hY : ∏ j ∈ (Finset.Icc 1 n).erase (m + 1), (y - -((j : ℂ) * c)) =
      ∏ j ∈ (Finset.Icc 1 n).erase (m + 1), (y + (j : ℂ) * c) :=
    Finset.prod_congr rfl fun j _ => by ring
  rw [hD, hY]
  simp only [Nat.add_sub_cancel]
  have hf1 : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hf2 : (Nat.factorial (n - (m + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hk0' : y + (c : ℂ) * ((m + 1 : ℕ) : ℂ) ≠ 0 := by rw [mul_comm]; exact hk0
  field_simp
  exact Finset.prod_congr rfl fun j _ => by ring

/-- The coefficients of the partial fractions against `turC`:
`(η^{2(n−1)} (−1)^{k−1} (k−1)! (n−k)!)⁻¹ = C_{n,k} η^{1−2n} √k η` for `k ∈ [1, n]`. -/
private lemma edgeSqrt_coef {n k : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n) {η : ℝ}
    (hη : 0 < η) :
    ((η ^ 2) ^ (n - 1) * ((-1) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ) *
      (Nat.factorial (n - k) : ℝ)))⁻¹ = turC n k * η ^ (1 - 2 * (n : ℤ)) * (√(k : ℝ) * η) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
  have hη' : η ^ (1 - 2 * (n : ℤ)) * η = ((η ^ 2) ^ (n - 1))⁻¹ := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have : (1 - 2 * ((n' + 1 : ℕ) : ℤ)) = -((2 * n' + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, _root_.zpow_neg, zpow_natCast]
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have h1 : (k : ℝ) ^ (-(1 / 2 : ℝ)) * √(k : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk0]
    norm_num
  have hs2 : ((-1 : ℝ) ^ (k - 1))⁻¹ = (-1) ^ (k - 1) := by
    rw [← inv_pow, inv_neg, inv_one]
  have e : turC n k * η ^ (1 - 2 * (n : ℤ)) * (√(k : ℝ) * η) =
      ((k : ℝ) ^ (-(1 / 2 : ℝ)) * √(k : ℝ)) * (η ^ (1 - 2 * (n : ℤ)) * η) *
        ((-1) ^ (k - 1) / ((Nat.factorial (k - 1) : ℝ) * (Nat.factorial (n - k) : ℝ))) := by
    unfold turC
    ring
  rw [e, h1, hη', one_mul]
  simp only [mul_inv, hs2, div_eq_mul_inv]
  ring

/-- (tur2) in contour form (§10, §12.4): for `f` holomorphic on the disc of radius `r` about a
real `E`, with `f(ζ̄) = conj f(ζ)` and `|f| ≤ K₀` there, and `nη² ≤ (r/2)²`,
`∑ₖ C_{n,k} η^{1−2n} Im f(E + i√k η) = (2πi)⁻¹ ∮_{|ζ−E| = 3r/4} f(ζ) ∏ₖ ((ζ − E)² + kη²)⁻¹ dζ`,
so that `|∑ₖ C_{n,k} η^{1−2n} Im f(E + i√k η)| ≤ K₀ 2ⁿ (3r/4)^{1−2n}`. -/
private lemma edgeSqrt_tur_contour {f : ℂ → ℂ} {E r K₀ η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hr : 0 < r) (hη : 0 < η) (hf : DifferentiableOn ℂ f (Metric.ball (E : ℂ) r))
    (hconj : ∀ ζ ∈ Metric.ball (E : ℂ) r, f ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (f ζ))
    (hK : ∀ ζ ∈ Metric.ball (E : ℂ) r, ‖f ζ‖ ≤ K₀) (hnη : (n : ℝ) * η ^ 2 ≤ (r / 2) ^ 2) :
    |∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) * (f ⟨E, √(k : ℝ) * η⟩).im| ≤
      K₀ * 2 ^ n * (3 * r / 4) ^ (1 - 2 * (n : ℤ)) := by
  set ρ := 3 * r / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hcl : Metric.closedBall (E : ℂ) ρ ⊆ Metric.ball (E : ℂ) r :=
    Metric.closedBall_subset_ball (by linarith)
  have hfc : DifferentiableOn ℂ f (Metric.closedBall (E : ℂ) ρ) := hf.mono hcl
  have hfcont : ContinuousOn f (Metric.sphere (E : ℂ) ρ) :=
    hfc.continuousOn.mono Metric.sphere_subset_closedBall
  set s : ℕ → ℝ := fun k => √(k : ℝ) * η with hs
  have hsk : ∀ k ∈ Finset.Icc 1 n, 0 < s k ∧ s k ^ 2 = k * η ^ 2 ∧ s k ≤ r / 2 := by
    intro k hk
    have hk1 := Finset.mem_Icc.1 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1.1
    have hsq : s k ^ 2 = k * η ^ 2 := by
      simp only [hs]; rw [mul_pow, Real.sq_sqrt hk0.le]
    refine ⟨by simp only [hs]; positivity, hsq, ?_⟩
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk1.2
    have : s k ^ 2 ≤ (r / 2) ^ 2 := by
      rw [hsq]; exact le_trans (mul_le_mul_of_nonneg_right hkn (sq_nonneg η)) hnη
    exact (pow_le_pow_iff_left₀ (by simp only [hs]; positivity) (by positivity)
      two_ne_zero).1 this
  set z : ℕ → ℂ := fun k => ⟨E, s k⟩ with hzdef
  have hz_eq : ∀ k, z k = (E : ℂ) + (s k : ℂ) * Complex.I := fun k =>
    Complex.ext (by simp [hzdef]) (by simp [hzdef])
  have hzc_eq : ∀ k, (starRingEnd ℂ) (z k) = (E : ℂ) - (s k : ℂ) * Complex.I := fun k => by
    rw [hz_eq, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hzb : ∀ k ∈ Finset.Icc 1 n, z k ∈ Metric.ball (E : ℂ) ρ ∧
      (starRingEnd ℂ) (z k) ∈ Metric.ball (E : ℂ) ρ := by
    intro k hk
    obtain ⟨h1, -, h3⟩ := hsk k hk
    have hn1 : ‖z k - E‖ = s k := by
      rw [hz_eq, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos h1]
    have hn2 : ‖(starRingEnd ℂ) (z k) - E‖ = s k := by
      rw [hzc_eq, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
    refine ⟨?_, ?_⟩ <;> rw [mem_ball_iff_norm]
    · rw [hn1]; linarith
    · rw [hn2]; linarith
  have hne_sph : ∀ ζ ∈ Metric.sphere (E : ℂ) ρ, ∀ k ∈ Finset.Icc 1 n,
      ζ - z k ≠ 0 ∧ ζ - (starRingEnd ℂ) (z k) ≠ 0 := by
    intro ζ hζ k hk
    obtain ⟨h1, h2⟩ := hzb k hk
    rw [mem_sphere_iff_norm] at hζ
    rw [mem_ball_iff_norm] at h1 h2
    constructor
    · intro h; rw [sub_eq_zero] at h; rw [h] at hζ; linarith
    · intro h; rw [sub_eq_zero] at h; rw [h] at hζ; linarith
  have hlow : ∀ ζ ∈ Metric.sphere (E : ℂ) ρ, ∀ k ∈ Finset.Icc 1 n,
      ρ ^ 2 / 2 ≤ ‖(ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ)‖ := by
    intro ζ hζ k hk
    obtain ⟨h1, h2, h3⟩ := hsk k hk
    rw [mem_sphere_iff_norm] at hζ
    have e1 : ‖(k : ℂ) * ((η ^ 2 : ℝ) : ℂ)‖ = k * η ^ 2 := by
      rw [show (k : ℂ) * ((η ^ 2 : ℝ) : ℂ) = ((k * η ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := norm_sub_norm_le ((ζ - E) ^ 2) (-((k : ℂ) * ((η ^ 2 : ℝ) : ℂ)))
    rw [sub_neg_eq_add, norm_neg, e1, norm_pow, hζ] at this
    have h4 : s k ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ h1.le h3 2
    have h5 : (r / 2) ^ 2 = 4 / 9 * ρ ^ 2 := by rw [hρ]; ring
    nlinarith
  have hfac : ∀ ζ : ℂ, ∀ k ∈ Finset.Icc 1 n,
      (ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ) = (ζ - z k) * (ζ - (starRingEnd ℂ) (z k)) := by
    intro ζ k hk
    obtain ⟨-, h2, -⟩ := hsk k hk
    have h2' : ((s k : ℝ) : ℂ) ^ 2 = (k : ℂ) * ((η ^ 2 : ℝ) : ℂ) := by exact_mod_cast h2
    rw [hzc_eq, hz_eq, ← h2']
    ring_nf
    rw [Complex.I_sq]
    ring
  -- partial fractions on the sphere
  set B : ℕ → ℂ := fun k => ((((η ^ 2 : ℝ)) : ℂ) ^ (n - 1) * ((-1) ^ (k - 1) *
    (Nat.factorial (k - 1) : ℂ) * (Nat.factorial (n - k) : ℂ)))⁻¹ with hB
  set g : ℕ → ℂ → ℂ := fun k ζ => (B k * (2 * (s k : ℂ) * Complex.I)⁻¹) •
    ((ζ - z k)⁻¹ • f ζ - (ζ - (starRingEnd ℂ) (z k))⁻¹ • f ζ) with hg
  have hpt : Set.EqOn (fun ζ => f ζ * ∏ k ∈ Finset.Icc 1 n,
      ((ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ))⁻¹)
      (fun ζ => ∑ k ∈ Finset.Icc 1 n, g k ζ) (Metric.sphere (E : ℂ) ρ) := by
    intro ζ hζ
    have hy : ∀ k ∈ Finset.Icc 1 n, (ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ) ≠ 0 := by
      intro k hk h
      have := hlow ζ hζ k hk
      rw [h, norm_zero] at this
      have : 0 < ρ ^ 2 / 2 := by positivity
      linarith
    simp only
    rw [edgeSqrt_pf hn (by positivity) hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := hne_sph ζ hζ k hk
    have hs0 : (s k : ℂ) ≠ 0 := by exact_mod_cast (hsk k hk).1.ne'
    simp only [hg, smul_eq_mul]
    rw [hfac ζ k hk]
    have hzz : z k - (starRingEnd ℂ) (z k) = 2 * (s k : ℂ) * Complex.I := by
      rw [hzc_eq, hz_eq]; ring
    have h2sI : 2 * (s k : ℂ) * Complex.I ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.I_ne_zero, or_false, false_or]
      exact hs0
    have hdiff : (ζ - z k)⁻¹ - (ζ - (starRingEnd ℂ) (z k))⁻¹ =
        (2 * (s k : ℂ) * Complex.I) * ((ζ - z k) * (ζ - (starRingEnd ℂ) (z k)))⁻¹ := by
      rw [← hzz]; field_simp; ring
    rw [show (B k * (2 * (s k : ℂ) * Complex.I)⁻¹) * ((ζ - z k)⁻¹ * f ζ -
        (ζ - (starRingEnd ℂ) (z k))⁻¹ * f ζ) = B k * f ζ * ((2 * (s k : ℂ) * Complex.I)⁻¹ *
        ((ζ - z k)⁻¹ - (ζ - (starRingEnd ℂ) (z k))⁻¹)) by ring, hdiff,
      inv_mul_cancel_left₀ h2sI, hB]
    ring
  have hci : ∀ k ∈ Finset.Icc 1 n, CircleIntegrable (fun ζ => (ζ - z k)⁻¹ • f ζ) E ρ ∧
      CircleIntegrable (fun ζ => (ζ - (starRingEnd ℂ) (z k))⁻¹ • f ζ) E ρ := by
    intro k hk
    constructor
    · refine ContinuousOn.circleIntegrable hρ0.le (ContinuousOn.fun_smul ?_ hfcont)
      exact (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => (hne_sph ζ hζ k hk).1
    · refine ContinuousOn.circleIntegrable hρ0.le (ContinuousOn.fun_smul ?_ hfcont)
      exact (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => (hne_sph ζ hζ k hk).2
  have hgi : ∀ k ∈ Finset.Icc 1 n, CircleIntegrable (g k) E ρ := by
    intro k hk
    simp only [hg]
    refine ContinuousOn.circleIntegrable hρ0.le
      (continuousOn_const.fun_smul (ContinuousOn.fun_sub ?_ ?_))
    · exact ContinuousOn.fun_smul ((continuousOn_id.sub continuousOn_const).inv₀
        fun ζ hζ => (hne_sph ζ hζ k hk).1) hfcont
    · exact ContinuousOn.fun_smul ((continuousOn_id.sub continuousOn_const).inv₀
        fun ζ hζ => (hne_sph ζ hζ k hk).2) hfcont
  set T := ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) * (f (z k)).im with hT
  have hint : (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(E, ρ), f ζ * ∏ k ∈ Finset.Icc 1 n,
      ((ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ))⁻¹ = (T : ℂ) := by
    rw [circleIntegral.integral_congr hρ0.le hpt, circleIntegral.integral_fun_sum hgi,
      Finset.smul_sum, hT, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [hg]
    rw [circleIntegral.integral_smul, circleIntegral.integral_sub (hci k hk).1 (hci k hk).2,
      hfc.circleIntegral_sub_inv_smul (hzb k hk).1, hfc.circleIntegral_sub_inv_smul (hzb k hk).2,
      hconj _ (hcl (Metric.ball_subset_closedBall (hzb k hk).1)), ← smul_sub, Complex.sub_conj]
    have hBk : B k = ((turC n k * η ^ (1 - 2 * (n : ℤ)) * s k : ℝ) : ℂ) := by
      rw [← edgeSqrt_coef hn hk hη]
      simp only [hB]
      push_cast
      ring
    have hs0 : (s k : ℂ) ≠ 0 := by exact_mod_cast (hsk k hk).1.ne'
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [hBk, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
  have hK0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK E (Metric.mem_ball_self hr))
  have hbound : ∀ ζ ∈ Metric.sphere (E : ℂ) ρ, ‖f ζ * ∏ k ∈ Finset.Icc 1 n,
      ((ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ K₀ * (2 / ρ ^ 2) ^ n := by
    intro ζ hζ
    rw [norm_mul, norm_prod]
    have h1 : ‖f ζ‖ ≤ K₀ := hK ζ (hcl (Metric.sphere_subset_closedBall hζ))
    have h2 : ∏ k ∈ Finset.Icc 1 n, ‖((ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ))⁻¹‖ ≤
        (2 / ρ ^ 2) ^ n := by
      calc ∏ k ∈ Finset.Icc 1 n, ‖((ζ - E) ^ 2 + (k : ℂ) * ((η ^ 2 : ℝ) : ℂ))⁻¹‖
          ≤ ∏ _k ∈ Finset.Icc 1 n, (2 / ρ ^ 2) := by
            refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k hk => ?_
            rw [norm_inv, ← inv_div]
            exact inv_anti₀ (by positivity) (hlow ζ hζ k hk)
        _ = (2 / ρ ^ 2) ^ n := by rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
    exact mul_le_mul h1 h2 (by positivity) hK0
  have hfin := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ0.le hbound
  rw [hint, Complex.norm_real, Real.norm_eq_abs] at hfin
  have hz : ρ ^ (1 - 2 * (n : ℤ)) = ρ * ((ρ ^ 2) ^ n)⁻¹ := by
    rw [zpow_sub₀ hρ0.ne', zpow_one, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul, div_eq_mul_inv]
  calc |T| ≤ ρ * (K₀ * (2 / ρ ^ 2) ^ n) := hfin
    _ = K₀ * 2 ^ n * ρ ^ (1 - 2 * (n : ℤ)) := by rw [hz, div_pow]; ring

/-- The counterpart of (tur2) for `m^W` without the Stieltjes representation of `ϱ^W` (§12.4):
to the right of `L₊`, `|∑ₖ C_{n,k} η^{−2n+1} Im m^W(E + i√k η)| ≤ K min(E − L₊, 1)^{1−2n}`
once `nη² ≤ (c min(E − L₊, 1))²`. -/
theorem im_mW_tur_le {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : Fin N → ℝ,
      (∀ i, |a i| ≤ τ⁻¹ - 2) → StandingBoundW τ a (domW τ N) → ∀ E η : ℝ, LpW a < E → 0 < η →
        (n : ℝ) * η ^ 2 ≤ (c * min (E - LpW a) 1) ^ 2 →
        |∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) * (mW a ⟨E, √(k : ℝ) * η⟩).im| ≤
          K * min (E - LpW a) 1 ^ (1 - 2 * (n : ℤ)) := by
  obtain ⟨c₀, K₀, hc₀, -, hK₀, N₀, h⟩ := mW_continuation_right hτ
  refine ⟨c₀ / 2, K₀ * 2 ^ n * (3 * c₀ / 4) ^ (1 - 2 * (n : ℤ)), by positivity, by positivity,
    N₀, fun N hN a ha hSB E η hE hη hnη => ?_⟩
  obtain ⟨f, hf, hfm, hconj, hb⟩ := h N hN a ha hSB E hE
  set m := min (E - LpW a) 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  have hr : 0 < c₀ * m := by positivity
  have hnη' : (n : ℝ) * η ^ 2 ≤ (c₀ * m / 2) ^ 2 := by
    have : c₀ / 2 * m = c₀ * m / 2 := by ring
    rwa [this] at hnη
  have key := edgeSqrt_tur_contour hn hr hη hf hconj hb hnη'
  have hsum : ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
      (mW a ⟨E, √(k : ℝ) * η⟩).im = ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
      (f ⟨E, √(k : ℝ) * η⟩).im := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 := Finset.mem_Icc.1 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1.1
    have hs0 : 0 < √(k : ℝ) * η := by positivity
    have hsq : (√(k : ℝ) * η) ^ 2 ≤ (c₀ * m / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hk0.le]
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk1.2
      exact le_trans (mul_le_mul_of_nonneg_right hkn (sq_nonneg η)) hnη'
    have hsle : √(k : ℝ) * η ≤ c₀ * m / 2 :=
      (pow_le_pow_iff_left₀ hs0.le (by positivity) two_ne_zero).1 hsq
    have hmem : (⟨E, √(k : ℝ) * η⟩ : ℂ) ∈ Metric.ball (E : ℂ) (c₀ * m) := by
      rw [mem_ball_iff_norm]
      have e : (⟨E, √(k : ℝ) * η⟩ : ℂ) - (E : ℂ) = ((√(k : ℝ) * η : ℝ) : ℂ) * Complex.I :=
        Complex.ext (by simp) (by simp)
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs0]
      linarith
    rw [hfm _ hmem hs0]
  rw [hsum]
  refine key.trans (le_of_eq ?_)
  rw [show 3 * (c₀ * m) / 4 = 3 * c₀ / 4 * m by ring, mul_zpow]
  ring

#print axioms Anisotropic.im_mW_sqrt_edge
#print axioms Anisotropic.mW_continuation_right
#print axioms Anisotropic.im_mW_tur_le

end Anisotropic
