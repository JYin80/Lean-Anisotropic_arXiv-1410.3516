import Mathlib

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Basic objects: φ, π, the distinct nonzero values, `f` (def_fx), `P_z` -/

/-- The dimensional ratio `φ = M / N`, (def_phi). -/
def phiRatio (M N : ℕ) : ℝ := (M : ℝ) / N

/-- The empirical spectral measure `π = M⁻¹ Σ_i δ_{σ_i}`, (def_pi). -/
def empMeasure (σ : Fin M → ℝ) : Measure ℝ :=
  ((M : ℝ≥0∞)⁻¹) • ∑ i, Measure.dirac (σ i)

/-- The distinct nonzero values `s_1 > ⋯ > s_n` of `σ` (as a finset, for `σ ≥ 0`). -/
def posVals (σ : Fin M → ℝ) : Finset ℝ :=
  (Finset.univ.image σ).filter (fun s => 0 < s)

/-- The weight `r_s = φ π({s}) = #{i | σ i = s} / N` (Appendix A). -/
def weight (N : ℕ) (σ : Fin M → ℝ) (s : ℝ) : ℝ :=
  ((Finset.univ.filter fun i => σ i = s).card : ℝ) / N

/-- `R = φ π((0,∞)) = #{i | 0 < σ i} / N`. -/
def massRatio (N : ℕ) (σ : Fin M → ℝ) : ℝ :=
  ((Finset.univ.filter fun i => 0 < σ i).card : ℝ) / N

/-- The upper half-plane `ℂ₊` as a set. -/
def upperHalf : Set ℂ := {z | 0 < z.im}

/-- The function `f` of (def_fx), `f(w) = -1/w + N⁻¹ Σ_i σ_i / (1 + σ_i w)`. -/
def fC (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) : ℂ :=
  -w⁻¹ + ∑ i, (σ i : ℂ) / (N * (1 + σ i * w))

/-- The restriction of `f` to the real line. -/
def fR (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  -x⁻¹ + ∑ i, σ i / (N * (1 + σ i * x))

/-- `f'` on `ℂ`, (f_der). -/
def fCDeriv (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) : ℂ :=
  (w ^ 2)⁻¹ - ∑ i, (σ i : ℂ) ^ 2 / (N * (1 + σ i * w) ^ 2)

/-- `f'` on `ℝ`, (f_der). -/
def fR1 (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  (x ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * (1 + σ i * x) ^ 2)

/-- `f''` on `ℝ`, (f_der). -/
def fR2 (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : ℝ :=
  -2 * (x ^ 3)⁻¹ + 2 * ∑ i, σ i ^ 3 / (N * (1 + σ i * x) ^ 3)

/-- The polynomial `P_z(w) = w Π_s (1 + s w) (f(w) - z)` of degree `n + 1` (Appendix A.1). -/
def scPoly (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : ℂ[X] :=
  -(∏ s ∈ posVals σ, (1 + C (s : ℂ) * X)) +
    X * ∑ s ∈ posVals σ, C ((weight N σ s * s : ℝ) : ℂ) *
      ∏ s' ∈ (posVals σ).erase s, (1 + C (s' : ℂ) * X) -
    C z * X * ∏ s ∈ posVals σ, (1 + C (s : ℂ) * X)

theorem fC_ofReal (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : fC N σ x = fR N σ x := by
  unfold fC fR
  push_cast
  rfl

/-- The identity `Im f(w) = Im w (|w|⁻² - N⁻¹ Σ_i σ_i² |1 + σ_i w|⁻²)`. -/
theorem im_fC (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) :
    (fC N σ w).im = w.im * ((‖w‖ ^ 2)⁻¹ - ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2)) := by
  have key : ∀ i, ((σ i : ℂ) / (N * (1 + σ i * w))).im
      = -(w.im * (σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * w‖ ^ 2))) := by
    intro i
    have h : (σ i : ℂ) / (N * (1 + σ i * w)) = ((σ i / N : ℝ) : ℂ) * (1 + σ i * w)⁻¹ := by
      push_cast; field_simp
    rw [h, Complex.im_ofReal_mul, Complex.inv_im, Complex.normSq_eq_norm_sq]
    simp
    ring
  unfold fC
  rw [Complex.add_im, Complex.neg_im, Complex.inv_im, Complex.im_sum]
  simp_rw [key]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Complex.normSq_eq_norm_sq]
  ring

theorem sum_weight (N : ℕ) (σ : Fin M → ℝ) :
    ∑ s ∈ posVals σ, weight N σ s = massRatio N σ := by
  unfold weight massRatio
  rw [← Finset.sum_div]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i => 0 < σ i), σ i ∈ posVals σ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [posVals, hi]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs0 : 0 < s := (Finset.mem_filter.mp hs).2
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => ⟨h ▸ hs0, h⟩
  · exact fun h => h.2

theorem massRatio_le_phiRatio (N : ℕ) (σ : Fin M → ℝ) : massRatio N σ ≤ phiRatio M N := by
  unfold massRatio phiRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have : (Finset.univ.filter fun i => 0 < σ i).card ≤ M := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun i => 0 < σ i)
  exact_mod_cast this

/-! ## Concrete instance (Marchenko–Pastur) -/

/-- MP: `posVals = {1}`, `r_1 = 1/2`. -/
example : posVals (fun _ : Fin 1 => (1 : ℝ)) = {1} := by
  ext s; simp [posVals]; rintro rfl; norm_num

example : weight 2 (fun _ : Fin 1 => (1 : ℝ)) 1 = 1 / 2 := by
  simp [weight]

/-- MP: `fC` at `w = i` equals `1/4 + 3/4 i`. -/
example : fC 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I = ⟨1 / 4, 3 / 4⟩ := by
  apply Complex.ext
  · simp [fC, Complex.inv_re, Complex.normSq]
    norm_num
  · simp [fC, Complex.inv_im, Complex.normSq]
    norm_num

/-- MP: the identities at one real point and at `w = i`. -/
example : fC 2 (fun _ : Fin 1 => (1 : ℝ)) ((-1 / (1 + Real.sqrt (1 / 2)) : ℝ) : ℂ) =
    fR 2 (fun _ : Fin 1 => (1 : ℝ)) (-1 / (1 + Real.sqrt (1 / 2))) :=
  fC_ofReal 2 _ _

example : ∑ s ∈ posVals (fun _ : Fin 1 => (1 : ℝ)), weight 2 (fun _ : Fin 1 => (1 : ℝ)) s =
    massRatio 2 (fun _ : Fin 1 => (1 : ℝ)) :=
  sum_weight 2 _

example : massRatio 2 (fun _ : Fin 1 => (1 : ℝ)) = 1 / 2 ∧ phiRatio 1 2 = 1 / 2 := by
  constructor <;> simp [massRatio, phiRatio]

example : massRatio 2 (fun _ : Fin 1 => (1 : ℝ)) ≤ phiRatio 1 2 :=
  massRatio_le_phiRatio 2 _

example : (fC 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I).im = Complex.I.im *
    ((‖Complex.I‖ ^ 2)⁻¹ - ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i ^ 2 /
      (2 * ‖1 + (((fun _ : Fin 1 => (1 : ℝ)) i : ℝ) : ℂ) * Complex.I‖ ^ 2)) :=
  im_fC 2 _ Complex.I


end Anisotropic
