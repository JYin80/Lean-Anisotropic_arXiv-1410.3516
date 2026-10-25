import Anisotropic.Density.Stability.Domains
import Anisotropic.Entrywise.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The scale ladder, level sets, the setting -/

/-- (def_L_eta): `L(η) = max{l ∈ ℕ : η N^{δ(l−1)} < 1}`, written as `⌈log(1/η)/(δ log N)⌉₊`. -/
def ladderL (N : ℕ) (δ η : ℝ) : ℕ := ⌈Real.log η⁻¹ / (δ * Real.log N)⌉₊

/-- (def_eta_k): `η_l = η N^{δl}` for `l < L(η)`, `η_l = 1` for `l ≥ L(η)`. -/
def ladderEta (N : ℕ) (δ η : ℝ) (l : ℕ) : ℝ :=
  if l < ladderL N δ η then η * (N : ℝ) ^ (δ * l) else 1

/-- The ladder point `E + i η_l` of `z = E + i η`. -/
def ladderPt (N : ℕ) (δ : ℝ) (z : ℂ) (l : ℕ) : ℂ := ⟨z.re, ladderEta N δ z.im l⟩

/-- `S_m = {z ∈ S : Im z ≥ N^{−δm}}` (the net-free form of `Ŝ_m`). -/
def levelSet (N : ℕ) (δ : ℝ) (S : Set ℂ) (m : ℕ) : Set ℂ :=
  {z | z ∈ S ∧ (N : ℝ) ^ (-(δ * m)) ≤ z.im}

/-- For real `t`: `η N^{δ(t−1)} < 1` iff `t − 1 < log(1/η)/(δ log N)`. -/
private lemma ladder_key {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η) (t : ℝ) :
    η * (N : ℝ) ^ (δ * (t - 1)) < 1 ↔ t - 1 < Real.log η⁻¹ / (δ * Real.log N) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlN : 0 < Real.log N := Real.log_pos hN1
  have hNp : 0 < (N : ℝ) := by linarith
  rw [lt_div_iff₀ (mul_pos hδ hlN), ← Real.log_neg_iff (mul_pos hη (Real.rpow_pos_of_pos hNp _)),
    Real.log_mul hη.ne' (Real.rpow_pos_of_pos hNp _).ne', Real.log_rpow hNp, Real.log_inv]
  constructor <;> intro h <;> nlinarith

private lemma ladder_neg_one_lt {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η)
    (hηN : η < (N : ℝ) ^ δ) : (-1 : ℝ) < Real.log η⁻¹ / (δ * Real.log N) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have h := (ladder_key hN hδ hη 0).1 (by
    rw [show δ * ((0 : ℝ) - 1) = -δ by ring, Real.rpow_neg hNp.le, ← div_eq_mul_inv,
      div_lt_one (Real.rpow_pos_of_pos hNp _)]
    exact hηN)
  linarith

theorem ladderL_spec {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η)
    (hηN : η < (N : ℝ) ^ δ) :
    η * (N : ℝ) ^ (δ * ((ladderL N δ η : ℝ) - 1)) < 1 ∧
      ∀ l : ℕ, η * (N : ℝ) ^ (δ * ((l : ℝ) - 1)) < 1 → l ≤ ladderL N δ η := by
  have hneg := ladder_neg_one_lt hN hδ hη hηN
  refine ⟨(ladder_key hN hδ hη _).2 ?_, fun l hl => ?_⟩
  · unfold ladderL
    rcases le_or_gt (Real.log η⁻¹ / (δ * Real.log N)) 0 with ha | ha
    · rw [Nat.ceil_eq_zero.2 ha]
      simpa using hneg
    · have := Nat.ceil_lt_add_one ha.le
      linarith
  · rcases Nat.eq_zero_or_pos l with rfl | hl0
    · exact Nat.zero_le _
    · have h := (ladder_key hN hδ hη _).1 hl
      have h2 : l - 1 < ladderL N δ η := by
        refine Nat.lt_ceil.2 ?_
        rw [Nat.cast_sub hl0]
        simpa using h
      omega

/-- `L(η) ≤ δ⁻¹ + 1` for `η ≥ N^{−1}` (Section 7, after (def_eta_k)). -/
theorem ladderL_le {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : (N : ℝ) ^ (-1 : ℝ) ≤ η) :
    (ladderL N δ η : ℝ) ≤ δ⁻¹ + 1 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hlN : 0 < Real.log N := Real.log_pos hN1
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hNp _) hη
  have h1 : Real.log η⁻¹ ≤ Real.log N := by
    rw [Real.log_inv, neg_le]
    have := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hη
    rw [Real.log_rpow hNp] at this
    linarith
  have ha : Real.log η⁻¹ / (δ * Real.log N) ≤ δ⁻¹ := by
    rw [div_le_iff₀ (mul_pos hδ hlN)]
    calc Real.log η⁻¹ ≤ Real.log N := h1
      _ = δ⁻¹ * (δ * Real.log N) := by field_simp
  have h2 : ladderL N δ η ≤ ⌈δ⁻¹⌉₊ := Nat.ceil_mono ha
  have h3 : ((⌈δ⁻¹⌉₊ : ℕ) : ℝ) < δ⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.2 hδ.le)
  have h4 : (ladderL N δ η : ℝ) ≤ ((⌈δ⁻¹⌉₊ : ℕ) : ℝ) := by exact_mod_cast h2
  linarith

private lemma ladder_rpow_succ {N : ℕ} {δ : ℝ} (hN : 1 < N) (η : ℝ) (l : ℕ) :
    η * (N : ℝ) ^ (δ * ((l + 1 : ℕ) : ℝ)) = (N : ℝ) ^ δ * (η * (N : ℝ) ^ (δ * (l : ℝ))) := by
  have hNp : 0 < (N : ℝ) := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    linarith
  rw [show δ * ((l + 1 : ℕ) : ℝ) = δ * (l : ℝ) + δ by push_cast; ring,
    Real.rpow_add hNp]
  ring

/-- Consecutive ladder points differ by at most `N^δ`; `η_L = 1`. -/
theorem ladderEta_succ_le {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η)
    (hηN : η < (N : ℝ) ^ δ) {l : ℕ} (hl : l < ladderL N δ η) :
    ladderEta N δ η (l + 1) ≤ (N : ℝ) ^ δ * ladderEta N δ η l := by
  unfold ladderEta
  simp only [hl, ↓reduceIte]
  by_cases h : l + 1 < ladderL N δ η
  · simp only [h, ↓reduceIte]
    rw [ladder_rpow_succ hN]
  · simp only [h, ↓reduceIte]
    have hL : ladderL N δ η = l + 1 := by omega
    have hspec := (ladderL_spec hN hδ hη hηN).2 (l + 2)
    rw [← ladder_rpow_succ hN]
    by_contra hlt
    rw [not_le] at hlt
    have := hspec (by
      rw [show δ * (((l + 2 : ℕ) : ℝ) - 1) = δ * ((l + 1 : ℕ) : ℝ) by push_cast; ring]
      exact hlt)
    omega

private lemma ladderEta_lt_one {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η)
    (hηN : η < (N : ℝ) ^ δ) {l : ℕ} (hl : l < ladderL N δ η) :
    η * (N : ℝ) ^ (δ * (l : ℝ)) < 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  refine lt_of_le_of_lt ?_ (ladderL_spec hN hδ hη hηN).1
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 ?_) hη.le
  have : (l : ℝ) + 1 ≤ ladderL N δ η := by exact_mod_cast hl
  nlinarith

private lemma ladderEta_le_one {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η)
    (hη1 : η ≤ 1) (l : ℕ) : ladderEta N δ η l ≤ 1 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hηN : η < (N : ℝ) ^ δ := lt_of_le_of_lt hη1 (Real.one_lt_rpow hN1 hδ)
  unfold ladderEta
  split_ifs with h
  · exact (ladderEta_lt_one hN hδ hη hηN h).le
  · exact le_rfl

/-- For `0 < η ≤ 1`: `η ≤ η_l ≤ 1`, and `l ↦ η_l` is nondecreasing. -/
theorem ladderEta_bounds {N : ℕ} {δ η : ℝ} (hN : 1 < N) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1)
    (l : ℕ) : η ≤ ladderEta N δ η l ∧ ladderEta N δ η l ≤ 1 ∧
      ladderEta N δ η l ≤ ladderEta N δ η (l + 1) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ladderEta_le_one hN hδ hη hη1 l, ?_⟩
  · unfold ladderEta
    split_ifs with h
    · have : (1 : ℝ) ≤ (N : ℝ) ^ (δ * (l : ℝ)) :=
        Real.one_le_rpow hN1.le (by positivity)
      nlinarith
    · exact hη1
  · by_cases h : l < ladderL N δ η
    · by_cases h' : l + 1 < ladderL N δ η
      · unfold ladderEta
        simp only [h, h', ↓reduceIte]
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1.le ?_) hη.le
        push_cast
        nlinarith
      · unfold ladderEta
        simp only [h', ↓reduceIte]
        exact (ladderEta_le_one hN hδ hη hη1 l).trans (by simp)
    · have h' : ¬ l + 1 < ladderL N δ η := by omega
      unfold ladderEta
      simp only [h, h', ↓reduceIte]
      exact le_rfl

/-- The standing hypotheses of §7 on `(τ, c, M, N, Σ, S)`. -/
structure CompSetting (τ c : ℝ) (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ) :
    Prop where
  pos : 0 < τ
  le_one : τ ≤ 1
  c_pos : 0 < c
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  sigma : SigmaAssumption τ Sig
  domain : SpectralDomain τ N S
  oneXm : OneXmOn c N (specOf Sig) S

/-- Spectral domains are closed under the ladder of `z` with `Im z ≤ 1`. -/
theorem ladderPt_mem {τ : ℝ} {N : ℕ} {S : Set ℂ} (hS : SpectralDomain τ N S) (hτ1 : τ ≤ 1)
    (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ∈ S) (hz1 : z.im ≤ 1) (l : ℕ) :
    ladderPt N δ z l ∈ S := by
  obtain ⟨h0, hn, hre, hη, him⟩ := hS.1 hz
  have hτ : 0 < τ := inv_pos.1 (lt_of_lt_of_le h0 him)
  have hτinv : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  obtain ⟨hb1, hb2, -⟩ := ladderEta_bounds hN hδ h0 hz1 l
  have hre' : (ladderPt N δ z l).re = z.re := rfl
  have him' : (ladderPt N δ z l).im = ladderEta N δ z.im l := rfl
  have hnorm : ‖z‖ ≤ ‖ladderPt N δ z l‖ := by
    by_contra hc
    rw [not_le] at hc
    have hsq := pow_lt_pow_left₀ hc (norm_nonneg _) (two_ne_zero)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre',
      him'] at hsq
    nlinarith
  refine hS.2 z hz _ ⟨by rw [him']; linarith, hn.trans hnorm, by rw [hre']; exact hre, ?_, ?_⟩
    hre' (by rw [him']; exact hb1)
  · rw [him']; exact hη.trans hb1
  · rw [him']; exact hb2.trans hτinv

/-- The ladder points `l ≥ 1` of `z ∈ S_m` lie in `S_{m−1}`. -/
theorem ladderPt_level {τ : ℝ} {N : ℕ} {S : Set ℂ} (hS : SpectralDomain τ N S) (hτ1 : τ ≤ 1)
    (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 1 ≤ m) {z : ℂ} (hz : z ∈ levelSet N δ S m)
    (hz1 : z.im ≤ 1) {l : ℕ} (hl : 1 ≤ l) : ladderPt N δ z l ∈ levelSet N δ S (m - 1) := by
  refine ⟨ladderPt_mem hS hτ1 hN hδ hz.1 hz1 l, ?_⟩
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have him' : (ladderPt N δ z l).im = ladderEta N δ z.im l := rfl
  rw [him', Nat.cast_sub hm, Nat.cast_one]
  unfold ladderEta
  split_ifs with h
  · have h1 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (δ * (l : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hN1.le ?_
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    have h2 : (N : ℝ) ^ (-(δ * ((m : ℝ) - 1))) = (N : ℝ) ^ (-(δ * (m : ℝ))) * (N : ℝ) ^ δ := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    have hz2 := hz.2
    have hpos : 0 < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hNp _
    have hpos2 : 0 < (N : ℝ) ^ (-(δ * (m : ℝ))) := Real.rpow_pos_of_pos hNp _
    rw [h2]
    calc (N : ℝ) ^ (-(δ * (m : ℝ))) * (N : ℝ) ^ δ ≤ z.im * (N : ℝ) ^ δ :=
          mul_le_mul_of_nonneg_right hz2 hpos.le
      _ ≤ z.im * (N : ℝ) ^ (δ * (l : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (lt_of_lt_of_le hpos2 hz2).le
  · refine Real.rpow_le_one_of_one_le_of_nonpos hN1.le ?_
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-! ## Instances -/

/-- The ladder of `η = 1` is empty (`L(1) = 0`). -/
example (N : ℕ) (δ : ℝ) : ladderL N δ 1 = 0 := by simp [ladderL]

/-- `ladderEta_bounds` at `N = 4`, `δ = 1/2`, `η = 1/4`, `l = 1`. -/
example : (1 / 4 : ℝ) ≤ ladderEta 4 (1 / 2) (1 / 4) 1 ∧ ladderEta 4 (1 / 2) (1 / 4) 1 ≤ 1 ∧
    ladderEta 4 (1 / 2) (1 / 4) 1 ≤ ladderEta 4 (1 / 2) (1 / 4) (1 + 1) :=
  ladderEta_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1

#print axioms ladderL_spec
#print axioms ladderL_le
#print axioms ladderEta_succ_le
#print axioms ladderEta_bounds
#print axioms ladderPt_mem
#print axioms ladderPt_level
#print axioms CompSetting

end Anisotropic
