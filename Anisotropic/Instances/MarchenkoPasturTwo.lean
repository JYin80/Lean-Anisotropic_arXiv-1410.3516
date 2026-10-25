import Anisotropic.Density.Basic
import Anisotropic.Density.Boundary
import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Varrho
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.Gaussian.Ensemble
import Anisotropic.Gaussian.Spectral
import Anisotropic.Instances.Models
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Qdot.Defs
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The instance `Σ = I_{2n}`, `N = n` (rank `Σ ≥ N`), and the counterexample to the literal Theorem 11.3 -/

section PhiGtOne

private lemma one_posVals {M : ℕ} (hM : 0 < M) : posVals (fun _ : Fin M => (1 : ℝ)) = {1} := by
  have hne : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  rw [posVals, Finset.image_const hne, Finset.filter_singleton]
  simp

private lemma one_weight {M : ℕ} (N : ℕ) :
    weight N (fun _ : Fin M => (1 : ℝ)) 1 = (M : ℝ) / N := by
  simp [weight]

/-- `p = 1` for `σ ≡ 1`. -/
theorem numBands_one {M : ℕ} (hM : 0 < M) (hN : 0 < N) :
    numBands N (fun _ : Fin M => (1 : ℝ)) = 1 := by
  have hS : (posVals (fun _ : Fin M => (1 : ℝ))).Nonempty := by
    rw [one_posVals hM]; exact Finset.singleton_nonempty 1
  have hc := card_innerCrit N _ (fun _ => zero_le_one) hN hS
  have hdeg : (critPoly N (fun _ : Fin M => (1 : ℝ))).natDegree ≤ 2 := by
    simp only [critPoly, one_posVals hM, Finset.prod_singleton,
      Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty]
    compute_degree!
  have hle : Multiset.card (innerCrit N (fun _ : Fin M => (1 : ℝ))) ≤ 2 :=
    (Multiset.card_le_card (Multiset.filter_le _ _)).trans
      ((Polynomial.card_roots' _).trans hdeg)
  omega

/-- `x₁ = −1/(1 + √φ)`. -/
private lemma one_xCrit {M : ℕ} (hM : 0 < M) (hN : 0 < N) (hMN : N < M) :
    (1 + Real.sqrt ((M : ℝ) / N)) * xCrit N (fun _ : Fin M => (1 : ℝ)) 1 = -1 := by
  have hS : (posVals (fun _ : Fin M => (1 : ℝ))).Nonempty := by
    rw [one_posVals hM]; exact Finset.singleton_nonempty 1
  have hc := (card_innerCrit N _ (fun _ => zero_le_one) hN hS).1
  rw [numBands_one hM hN] at hc
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp (by omega :
    Multiset.card (innerCrit N (fun _ : Fin M => (1 : ℝ))) = 1)
  have hxc : xCrit N (fun _ : Fin M => (1 : ℝ)) 1 = x := by
    simp [xCrit, numBands_one hM hN, hx]
  have hm : x ∈ innerCrit N (fun _ : Fin M => (1 : ℝ)) := by
    rw [hx]; exact Multiset.mem_singleton_self x
  rw [hxc]
  unfold innerCrit at hm
  rw [Multiset.mem_filter, Polynomial.mem_roots'] at hm
  obtain ⟨⟨-, hroot⟩, hx0, s, hs, h1⟩ := hm
  rw [one_posVals hM, Finset.mem_singleton] at hs
  subst hs
  have h0 : (critPoly N (fun _ : Fin M => (1 : ℝ))).eval x = 0 := hroot
  simp only [critPoly, one_posVals hM, Finset.prod_singleton, Finset.sum_singleton,
    Finset.erase_singleton, Finset.prod_empty, one_weight, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X] at h0
  set w := (M : ℝ) / N with hw
  have hw1 : 1 < w := by rw [hw, one_lt_div (by exact_mod_cast hN)]; exact_mod_cast hMN
  have hs2 : Real.sqrt w ^ 2 = w := Real.sq_sqrt (by linarith)
  have hs1 : 1 < Real.sqrt w := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hw1
  have h : (1 + x - Real.sqrt w * x) * (1 + x + Real.sqrt w * x) = 0 := by
    linear_combination h0 - x ^ 2 * hs2
  rcases mul_eq_zero.mp h with h | h
  · nlinarith
  · linear_combination h

private lemma one_yEdge {M : ℕ} (hM : 0 < M) (hN : 0 < N) :
    yEdge N (fun _ : Fin M => (1 : ℝ)) = Real.sqrt ((M : ℝ) / N) - 1 := by
  have hS : (posVals (fun _ : Fin M => (1 : ℝ))).Nonempty := by
    rw [one_posVals hM]; exact Finset.singleton_nonempty 1
  obtain ⟨hin, h1⟩ := yEdge_spec N _ (fun _ => zero_le_one) hN hS
  have hy := hin 1 (by rw [one_posVals hM]; exact Finset.mem_singleton_self 1)
  simp only [FChart1, one_posVals hM, Finset.sum_singleton, one_weight] at h1
  set y := yEdge N (fun _ : Fin M => (1 : ℝ))
  have hw0 : 0 ≤ (M : ℝ) / N := by positivity
  have hne : y + 1 ≠ 0 := hy.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (y + 1) ^ 2 = (M : ℝ) / N := by
    field_simp at h1
    rw [eq_div_iff hNr]; linarith
  have : y + 1 = Real.sqrt ((M : ℝ) / N) := by
    rw [← h2, Real.sqrt_sq hy.le]
  linarith

private lemma one_fR {M : ℕ} (x : ℝ) :
    fR N (fun _ : Fin M => (1 : ℝ)) x = -x⁻¹ + ((M : ℝ) / N) / (1 + x) := by
  simp [fR, Finset.sum_const]
  ring

/-- `a₁ = (1 + √φ)²`. -/
theorem edgeVal_one_one {M : ℕ} (hM : 0 < M) (hN : 0 < N) (hMN : N < M) :
    edgeVal N (fun _ : Fin M => (1 : ℝ)) 1 = (1 + Real.sqrt ((M : ℝ) / N)) ^ 2 := by
  have hx := one_xCrit hM hN hMN
  have hw1 : 1 < (M : ℝ) / N := by
    rw [one_lt_div (by exact_mod_cast hN)]; exact_mod_cast hMN
  set s := Real.sqrt ((M : ℝ) / N) with hsdef
  have hs2 : s ^ 2 = (M : ℝ) / N := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have he : edgeVal N (fun _ : Fin M => (1 : ℝ)) 1 =
      fR N (fun _ : Fin M => (1 : ℝ)) (xCrit N (fun _ : Fin M => (1 : ℝ)) 1) := by
    simp [edgeVal, numBands_one hM hN]
  set x := xCrit N (fun _ : Fin M => (1 : ℝ)) 1
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hxinv : x⁻¹ = -(1 + s) := by
    have : x = -(1 + s)⁻¹ := by
      have h1s : (1 + s) ≠ 0 := by positivity
      field_simp; linarith
    rw [this, inv_neg, inv_inv]
  have h1x : 1 + x = s / (1 + s) := by
    field_simp; linarith
  rw [he, one_fR, hxinv, h1x, ← hs2]
  field_simp

/-- `a₂ = (√φ − 1)²`. -/
theorem edgeVal_one_two {M : ℕ} (hM : 0 < M) (hN : 0 < N) :
    edgeVal N (fun _ : Fin M => (1 : ℝ)) 2 = (Real.sqrt ((M : ℝ) / N) - 1) ^ 2 := by
  have hw0 : 0 ≤ (M : ℝ) / N := by positivity
  set s := Real.sqrt ((M : ℝ) / N) with hsdef
  have hs2 : s ^ 2 = (M : ℝ) / N := Real.sq_sqrt hw0
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have h1 : s - 1 + 1 ≠ 0 := by rw [sub_add_cancel]; positivity
  simp only [edgeVal, numBands_one hM hN, mul_one, ↓reduceIte, FChart,
    one_posVals hM, Finset.sum_singleton, one_weight, one_yEdge hM hN]
  rw [← hsdef, ← hs2]
  field_simp
  ring

end PhiGtOne

section PhiTwo

private lemma two_ratio {n : ℕ} (hn : 0 < n) : ((2 * n : ℕ) : ℝ) / n = 2 := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp

private lemma sqrt_two_bounds : 1.41 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

/-- `a₁ = (1 + √2)²` at `φ = 2`. -/
theorem edgeVal_two_one {n : ℕ} (hn : 0 < n) :
    edgeVal n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 = (1 + Real.sqrt 2) ^ 2 := by
  rw [edgeVal_one_one (by omega) hn (by omega), two_ratio hn]

/-- `a₂ = (√2 − 1)²` at `φ = 2`. -/
theorem edgeVal_two_two {n : ℕ} (hn : 0 < n) :
    edgeVal n (fun _ : Fin (2 * n) => (1 : ℝ)) 2 = (Real.sqrt 2 - 1) ^ 2 := by
  rw [edgeVal_one_two (by omega) hn, two_ratio hn]

/-- `Σ = I` satisfies the eigenvalue conditions of Assumption 2.1 at every `τ ∈ (0, 1)`. -/
theorem sigmaAssumption_one {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (M : ℕ) :
    SigmaAssumption τ (1 : Matrix (Fin M) (Fin M) ℝ) where
  posDef := Matrix.PosDef.one
  eigenvalues_le := fun i => by
    rw [eigenvalues_one]
    exact one_le_inv_iff₀.mpr ⟨hτ, hτ1.le⟩
  gap := by
    have h : {i : Fin M | (Matrix.PosDef.one :
        (1 : Matrix (Fin M) (Fin M) ℝ).PosDef).isHermitian.eigenvalues i
          ∈ Set.Icc 0 τ} = ∅ := by
      ext i
      simp only [eigenvalues_one, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]
      exact fun _ => hτ1
    rw [h]
    simp only [Set.ncard_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ 1 - τ := by linarith
    positivity

/-- Assumption 2.1 for Gaussian `X`, `Σ = I_{2n}`, `N = n`, `τ = 1/10`. -/
theorem isModel_two {n : ℕ} (hn : 1 ≤ n) :
    IsModel (1 / 10) gaussMoment (2 * n) n (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
      (gaussX (2 * n) n) :=
  isModel_gaussX hn (by rw [two_ratio (by omega)]; norm_num)
    (by rw [two_ratio (by omega)]; norm_num) (sigmaAssumption_one (by norm_num) (by norm_num) (2 * n))

/-- (bound_Sigma), (Sigma_gap) and `τ ≤ φ ≤ τ⁻¹` at `σ ≡ 1`, `φ = 2`, `τ = 1/10`. -/
theorem densityAssumptions_two {n : ℕ} (hn : 1 ≤ n) :
    DensityAssumptions (1 / 10) n (fun _ : Fin (2 * n) => (1 : ℝ)) := by
  have h := (isModel_two hn).diagModel_specOf.densityAssumptions (by norm_num)
  rwa [specOf_one_eq] at h

/-- `N_1 = n` (Lemma A.1). -/
theorem bandCount_two {n : ℕ} (hn : 0 < n) :
    bandCount n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 = n := by
  have h := (Ni_sum n (fun _ : Fin (2 * n) => (1 : ℝ)) (fun _ => one_pos) hn (by omega)).2
  rw [numBands_one (by omega) hn, Finset.Icc_self, Finset.sum_singleton] at h
  rw [h]
  push_cast
  exact min_eq_left (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)

/-- `N_1 = n` as a natural number. -/
theorem bandNat_two {n : ℕ} (hn : 0 < n) :
    bandNat n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 = n := by
  rw [bandNat, bandCount_two hn, Nat.floor_natCast]

/-- `d_0 = 0`. -/
theorem cumCount_zero' (N : ℕ) (σ : Fin M → ℝ) : cumCount N σ 0 = 0 := by
  simp [cumCount]

/-- `γ_{1,i} > a₂ = (√2 − 1)²` for every `i ≤ N_1 = n`. -/
theorem gammaBand_two_gt {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    (Real.sqrt 2 - 1) ^ 2 < gammaBand n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 i := by
  have h := gammaBand_mem (densityAssumptions_two hn) (fun _ => one_pos) le_rfl
    (by rw [numBands_one (by omega) (by omega)]) hi (by rw [bandNat_two (by omega)]; exact hin)
  rw [show 2 * 1 = 2 from rfl, edgeVal_two_two (by omega)] at h
  exact h.1

/-- `n^{1/3} · 1 · n^{−2/3} ≤ 1/6` for `n ≥ 216`. -/
private lemma rigBound_bottom_le {n : ℕ} (hn : 216 ≤ n) :
    rigBound n n n (1 / 3) ≤ 1 / 6 := by
  have hn0 : (0 : ℝ) < n := by have : (216 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  have hmin : min n (n + 1 - n) = 1 := by omega
  unfold rigBound
  rw [hmin, Nat.cast_one, Real.one_rpow, mul_one, ← Real.rpow_add hn0]
  rw [show (1 / 3 : ℝ) + -(2 / 3) = -(1 / 3) by norm_num, Real.rpow_neg hn0.le]
  have h6 : (6 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h216 : (216 : ℝ) ≤ n := by exact_mod_cast hn
    calc (6 : ℝ) = (216 : ℝ) ^ (1 / 3 : ℝ) := by
          rw [show (216 : ℝ) = 6 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) h216 (by norm_num)
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

/-- Theorem 11.3 with the classical quantities of `N` fails at the bottom index `(1, N)` for every sample:
`λ̇_N = 0` while `γ_{1,N} > (√2 − 1)² > N^{1/3 − 2/3}`. -/
theorem literal_bottom_fails {n : ℕ} (hn : 216 ≤ n) (Xm : Matrix (Fin (2 * n)) (Fin n) ℝ) :
    rigBound n (bandNat n (fun _ : Fin (2 * n) => (1 : ℝ)) 1) n (1 / 3) <
      |sortedEig (QdotN (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) Xm)
          (cumCount n (fun _ : Fin (2 * n) => (1 : ℝ)) (1 - 1) + n) -
        gammaBand n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 n| := by
  have hn1 : 1 ≤ n := by omega
  rw [bandNat_two (by omega), Nat.sub_self, cumCount_zero', zero_add,
    sortedEig_QdotN_last Matrix.PosSemidef.one Xm hn1, zero_sub, abs_neg]
  have hγ := gammaBand_two_gt hn1 hn1 le_rfl
  have hb := rigBound_bottom_le hn
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have hpos : 0 < gammaBand n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 n := lt_of_le_of_lt (sq_nonneg _) hγ
  rw [abs_of_pos hpos]
  nlinarith

end PhiTwo

section PhiTwoReg

private lemma two_xCrit {n : ℕ} (hn : 0 < n) :
    (1 + Real.sqrt 2) * xCrit n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 = -1 := by
  have h := one_xCrit (M := 2 * n) (N := n) (by omega) hn (by omega)
  rwa [two_ratio hn] at h

private lemma two_yEdge {n : ℕ} (hn : 0 < n) :
    yEdge n (fun _ : Fin (2 * n) => (1 : ℝ)) = Real.sqrt 2 - 1 := by
  rw [one_yEdge (by omega) hn, two_ratio hn]

/-- Both edges are regular (Definition 2.7 (i)) at `τ/2 = 1/20` for `φ = 2`. -/
theorem regularEdge_two {n : ℕ} (hn : 0 < n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    RegularEdge (1 / 10 / 2) n (fun _ : Fin (2 * n) => (1 : ℝ)) k := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp := numBands_one (M := 2 * n) (by omega) hn
  have e1 := edgeVal_two_one hn
  have e2 := edgeVal_two_two hn
  refine ⟨hk1, by rw [hp]; omega, ?_, ?_, ?_⟩
  · interval_cases k
    · rw [e1]; nlinarith
    · rw [e2]; nlinarith
  · intro l hl1 hl2 hlk
    rw [hp] at hl2
    interval_cases k <;> interval_cases l <;> simp at hlk <;>
      first
      | (rw [e1, e2, abs_of_pos (by nlinarith)]; nlinarith)
      | (rw [e1, e2, abs_of_neg (by nlinarith)]; nlinarith)
  · intro _ s hs
    rw [one_posVals (by omega), Finset.mem_singleton] at hs
    subst hs
    rw [inv_one]
    interval_cases k
    · have hx := two_xCrit hn
      set x := xCrit n (fun _ : Fin (2 * n) => (1 : ℝ)) 1
      have : x = -1 / (1 + Real.sqrt 2) := by
        field_simp; linarith
      have hx1 : 0 < x + 1 := by
        rw [this, div_add_one (by positivity), lt_div_iff₀ (by positivity)]; linarith
      rw [abs_of_pos hx1]
      have : -1 / (1 + Real.sqrt 2) ≥ -1 / 2 := by
        rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      linarith
    · have hx : xCrit n (fun _ : Fin (2 * n) => (1 : ℝ)) 2 = (Real.sqrt 2 - 1)⁻¹ := by
        simp [xCrit, hp, two_yEdge hn]
      rw [hx]
      have hpos : 0 < (Real.sqrt 2 - 1)⁻¹ := inv_pos.mpr (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith

/-- The equation `E m² + (E − 1) m + 1 = 0` for `m = m(E + i0)`, `E ≠ 0`, at `φ = 2`. -/
private lemma two_sc {n : ℕ} (hn : 0 < n) {E : ℝ} (hE : E ≠ 0) :
    (E : ℂ) * mExt n (fun _ : Fin (2 * n) => (1 : ℝ)) E ^ 2 +
      ((E : ℂ) - 1) * mExt n (fun _ : Fin (2 * n) => (1 : ℝ)) E + 1 = 0 := by
  have h := scPoly_eval_mExt n (fun _ : Fin (2 * n) => (1 : ℝ)) (fun _ => zero_le_one) hE
  simp only [scPoly, one_posVals (show 0 < 2 * n by omega), Finset.prod_singleton,
    Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, one_weight, two_ratio hn,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X] at h
  push_cast at h
  linear_combination -h

/-- On `[a₂ + t, a₁ − t]`: `min(t, 1)/50 ≤ ρ(E)`; with `m(E + i0) = u + iv`,
`4E²v² = (a₁ − E)(E − a₂) ≥ 2√2 t`. -/
private lemma two_rhoDens_ge {n : ℕ} (hn : 0 < n) {t E : ℝ} (ht : 0 < t)
    (hE1 : (Real.sqrt 2 - 1) ^ 2 + t ≤ E) (hE2 : E ≤ (1 + Real.sqrt 2) ^ 2 - t) :
    min t 1 / 50 ≤ rhoDens n (fun _ : Fin (2 * n) => (1 : ℝ)) E := by
  obtain ⟨hsl, hsu⟩ := sqrt_two_bounds
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hE0 : 0 < E := by nlinarith
  have hsc := two_sc hn hE0.ne'
  have hv0 := im_mExt_nonneg n (fun _ : Fin (2 * n) => (1 : ℝ)) (fun _ => zero_le_one) hE0.ne'
  set w := mExt n (fun _ : Fin (2 * n) => (1 : ℝ)) E
  have hre := congrArg Complex.re hsc
  have him := congrArg Complex.im hsc
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_re,
    Complex.zero_im, Complex.sub_re, Complex.sub_im] at hre him
  set u := w.re
  set v := w.im
  set D := ((1 + Real.sqrt 2) ^ 2 - E) * (E - (Real.sqrt 2 - 1) ^ 2) with hD_def
  have hD : 4 * E - (E - 1) ^ 2 = D := by
    rw [hD_def]; ring_nf; rw [hs2]; ring_nf
    have h4 : Real.sqrt 2 ^ 4 = 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2]; norm_num
    rw [h4]; ring
  have hDt : 2 * Real.sqrt 2 * t ≤ D := by
    have h1 : 0 ≤ (1 + Real.sqrt 2) ^ 2 - E - t := by linarith
    have h2 : 0 ≤ E - (Real.sqrt 2 - 1) ^ 2 - t := by linarith
    have hsum : (1 + Real.sqrt 2) ^ 2 - (Real.sqrt 2 - 1) ^ 2 = 4 * Real.sqrt 2 := by ring
    rw [hD_def]
    nlinarith [mul_nonneg h1 h2, mul_nonneg ht.le h1, mul_nonneg ht.le h2]
  have hDpos : 0 < D := by nlinarith
  have hv : 0 < v := by
    rcases hv0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hre
      nlinarith [sq_nonneg (2 * E * u + E - 1)]
  have hu : 2 * E * u + E - 1 = 0 := by
    have h : v * (2 * E * u + E - 1) = 0 := by linear_combination him
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hv.ne'
    · exact h
  have hv2 : 4 * E ^ 2 * v ^ 2 = D := by
    linear_combination (-(4 : ℝ) * E) * hre + (2 * E * u + E - 1) * hu + hD
  have hm0 : 0 < min t 1 := lt_min ht one_pos
  have hm2 : min t 1 ^ 2 ≤ t := by
    nlinarith [min_le_left t 1, min_le_right t 1]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 ≤ 10 := by
    have : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ hpi0.le hpi.le 2
    norm_num at this ⊢; linarith
  have hEle : E ≤ 6 := by
    have : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by ring_nf; rw [hs2]; ring
    linarith
  have hE2' : E ^ 2 ≤ 36 := by nlinarith
  have hlhs : (min t 1 * Real.pi) ^ 2 ≤ 10 * t := by
    rw [mul_pow]
    nlinarith [sq_nonneg (min t 1), sq_nonneg Real.pi]
  have hrhs : 2.8 * t ≤ 144 * v ^ 2 := by
    have ha : 2.8 * t ≤ 2 * Real.sqrt 2 * t := by
      have : 0 ≤ (2 * Real.sqrt 2 - 2.8) * t := mul_nonneg (by linarith) ht.le
      linarith
    have hb : 4 * E ^ 2 * v ^ 2 ≤ 144 * v ^ 2 := by
      have : 0 ≤ (36 - E ^ 2) * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg v)
      linarith
    linarith
  rw [rhoDens, le_div_iff₀ hpi0]
  refine (pow_le_pow_iff_left₀ (by positivity) hv.le two_ne_zero).mp ?_
  have he : (min t 1 / 50 * Real.pi) ^ 2 = (min t 1 * Real.pi) ^ 2 / 2500 := by ring
  rw [he]
  have := sq_nonneg v
  linarith

/-- The bulk component is regular (Definition 2.7 (ii)) with `c(t) = min(t, 1)/50` for `φ = 2`. -/
theorem regularBulk_two {n : ℕ} (hn : 0 < n) :
    RegularBulk (fun t => min t 1 / 50) n (fun _ : Fin (2 * n) => (1 : ℝ)) 1 := by
  refine ⟨le_rfl, by rw [numBands_one (by omega) hn], fun t ht => ⟨?_, fun E hE => ?_⟩⟩
  · exact div_pos (lt_min ht one_pos) (by norm_num)
  · rw [show 2 * 1 = 2 from rfl, show 2 * 1 - 1 = 1 from rfl, edgeVal_two_two hn,
      edgeVal_two_one hn] at hE
    exact two_rhoDens_ge hn ht hE.1 hE.2

end PhiTwoReg

section PhiTwoFacts

/-- Theorem 11.3 with the classical quantities of `N` at every index is false:
at `Σ = I_{2n}`, `N = n`, Gaussian `X`, `τ = 1/10`, `c(t) = min(t,1)/50`, `ε = 1/3`, `D = 1`, every
hypothesis of Theorem 3.12 holds and the event is empty for `n ≥ 216`. -/
theorem rigidity_dot_literal_false :
    ¬ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel (1 / 10) gaussMoment M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → 1 / 10 / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (1 / 10 / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
        RegularBulk (fun t => min t 1 / 50) N (specOf Sig) k) →
      HighProbAt N 1 {ω | ∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
        ∀ i, 1 ≤ i → i ≤ bandNat N (specOf Sig) k → 1 / 10 ≤ gammaBand N (specOf Sig) k i →
          |sortedEig (QdotN Sig (X ω)) (cumCount N (specOf Sig) (k - 1) + i) -
              gammaBand N (specOf Sig) k i| ≤
            rigBound N (bandNat N (specOf Sig) k) i (1 / 3)} := by
  rintro ⟨N₀, h⟩
  set n := max N₀ 216 with hn
  have hn216 : 216 ≤ n := le_max_right _ _
  have hn1 : 1 ≤ n := by omega
  have hσ : specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) = fun _ => 1 := specOf_one_eq _
  have hp1 : numBands n (fun _ : Fin (2 * n) => (1 : ℝ)) = 1 := numBands_one (by omega) (by omega)
  have hp := h n (le_max_left _ _) (2 * n) 1 (gaussX (2 * n) n) (isModel_two hn1)
    (by
      intro k hk1 hk2 _
      rw [hσ] at hk2 ⊢
      rw [hp1] at hk2
      exact regularEdge_two (by omega) hk1 (by omega))
    (by
      intro k hk1 hk2
      rw [hσ] at hk2 ⊢
      rw [hp1] at hk2
      obtain rfl : k = 1 := by omega
      exact regularBulk_two (by omega))
  unfold HighProbAt at hp
  have hsub : (Set.univ : Set (GaussSpace (2 * n) n)) ⊆ {ω | ∀ k, 1 ≤ k →
      k ≤ numBands n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) →
      ∀ i, 1 ≤ i → i ≤ bandNat n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k →
        1 / 10 ≤ gammaBand n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k i →
        |sortedEig (QdotN 1 (gaussX (2 * n) n ω))
            (cumCount n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) (k - 1) + i) -
          gammaBand n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k i| ≤
        rigBound n (bandNat n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) k) i
          (1 / 3)}ᶜ := by
    intro ω _ hω
    rw [Set.mem_ofPred_eq, hσ] at hω
    obtain ⟨h1, h2⟩ := sqrt_two_bounds
    have hγ := gammaBand_two_gt hn1 hn1 le_rfl
    have := hω 1 le_rfl (by rw [hp1]) n hn1 (by rw [bandNat_two (by omega)])
      (by nlinarith)
    exact absurd this (not_le.mpr (literal_bottom_fails hn216 (gaussX (2 * n) n ω)))
  have h1 := (measure_mono hsub).trans hp
  rw [measure_univ, ENNReal.one_le_ofReal] at h1
  have hn0 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have : (n : ℝ) ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]; exact inv_lt_one_of_one_lt₀ hn0
  linarith

end PhiTwoFacts

section Witnesses

example : numBands 10 (fun _ : Fin 20 => (1 : ℝ)) = 1 :=
  numBands_one (by norm_num) (by norm_num)

example : edgeVal 10 (fun _ : Fin 20 => (1 : ℝ)) 1 = (1 + Real.sqrt ((20 : ℕ) / (10 : ℕ))) ^ 2 :=
  edgeVal_one_one (by norm_num) (by norm_num) (by norm_num)

example : edgeVal 10 (fun _ : Fin 20 => (1 : ℝ)) 2 = (Real.sqrt ((20 : ℕ) / (10 : ℕ)) - 1) ^ 2 :=
  edgeVal_one_two (by norm_num) (by norm_num)

example : edgeVal 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 1 = (1 + Real.sqrt 2) ^ 2 :=
  edgeVal_two_one (by norm_num)

example : edgeVal 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 2 = (Real.sqrt 2 - 1) ^ 2 :=
  edgeVal_two_two (by norm_num)

example : SigmaAssumption (1 / 10) (1 : Matrix (Fin 20) (Fin 20) ℝ) :=
  sigmaAssumption_one (by norm_num) (by norm_num) 20

example : IsModel (1 / 10) gaussMoment (2 * 10) 10
    (1 : Matrix (Fin (2 * 10)) (Fin (2 * 10)) ℝ) (gaussX (2 * 10) 10) :=
  isModel_two (by norm_num)

example : DensityAssumptions (1 / 10) 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) :=
  densityAssumptions_two (by norm_num)

example : bandCount 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 1 = 10 :=
  bandCount_two (by norm_num)

example : bandNat 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 1 = 10 :=
  bandNat_two (by norm_num)

example : (Real.sqrt 2 - 1) ^ 2 < gammaBand 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 1 1 :=
  gammaBand_two_gt (by norm_num) le_rfl (by norm_num)

example : rigBound 216 (bandNat 216 (fun _ : Fin (2 * 216) => (1 : ℝ)) 1) 216 (1 / 3) <
    |sortedEig (QdotN (1 : Matrix (Fin (2 * 216)) (Fin (2 * 216)) ℝ)
        (0 : Matrix (Fin (2 * 216)) (Fin 216) ℝ))
        (cumCount 216 (fun _ : Fin (2 * 216) => (1 : ℝ)) (1 - 1) + 216) -
      gammaBand 216 (fun _ : Fin (2 * 216) => (1 : ℝ)) 1 216| :=
  literal_bottom_fails (by norm_num) (0 : Matrix (Fin (2 * 216)) (Fin 216) ℝ)

example : RegularEdge (1 / 10 / 2) 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 1 :=
  regularEdge_two (by norm_num) le_rfl (by norm_num)

example : RegularEdge (1 / 10 / 2) 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 2 :=
  regularEdge_two (by norm_num) (by norm_num) le_rfl

example : RegularBulk (fun t => min t 1 / 50) 10 (fun _ : Fin (2 * 10) => (1 : ℝ)) 1 :=
  regularBulk_two (by norm_num)

end Witnesses

#print axioms numBands_one
#print axioms edgeVal_one_one
#print axioms edgeVal_one_two
#print axioms edgeVal_two_one
#print axioms edgeVal_two_two
#print axioms sigmaAssumption_one
#print axioms isModel_two
#print axioms densityAssumptions_two
#print axioms bandCount_two
#print axioms bandNat_two
#print axioms cumCount_zero'
#print axioms gammaBand_two_gt
#print axioms literal_bottom_fails
#print axioms regularEdge_two
#print axioms regularBulk_two
#print axioms rigidity_dot_literal_false
end Anisotropic
