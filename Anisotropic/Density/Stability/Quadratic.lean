import Anisotropic.Density.Stability.Domains

/-!
# The quadratic equation for `m`

Higher derivatives of `f` (f_der), the quadratic identity (quadr_edge) with the coefficients
`α`, `β` of (def_al_be), the selection of the small root, the imaginary-part identity
(im_def_m), and the passage from (mz_reg) to (1+xm).
-/

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Higher derivatives of `f`, (f_der) -/

/-- `f''` on `ℂ`, (f_der). -/
def fCDeriv2 (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) : ℂ :=
  -2 * (w ^ 3)⁻¹ + 2 * ∑ i, (σ i : ℂ) ^ 3 / (N * (1 + σ i * w) ^ 3)

/-- `f'''` on `ℂ`, (f_der). -/
def fCDeriv3 (N : ℕ) (σ : Fin M → ℝ) (w : ℂ) : ℂ :=
  6 * (w ^ 4)⁻¹ - 6 * ∑ i, (σ i : ℂ) ^ 4 / (N * (1 + σ i * w) ^ 4)

private lemma quad_hasDerivAt_inv_pow (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun w : ℂ => (w ^ k)⁻¹) (-(k : ℂ) * (w ^ (k + 1))⁻¹) w := by
  have h1 : HasDerivAt (fun w : ℂ => w ^ k) (((k : ℕ) : ℂ) * w ^ (k - 1)) w :=
    hasDerivAt_pow k w
  have h := h1.inv (pow_ne_zero k hw)
  convert h using 1
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

private lemma quad_hasDerivAt_term (k : ℕ) (a n : ℂ) {w : ℂ} (h : 1 + a * w ≠ 0) :
    HasDerivAt (fun w : ℂ => a ^ k / (n * (1 + a * w) ^ k))
      (-((k : ℂ) * (a ^ (k + 1) / (n * (1 + a * w) ^ (k + 1))))) w := by
  have h1 : HasDerivAt (fun w : ℂ => 1 + a * w) a w := by
    simpa using ((hasDerivAt_id w).const_mul a).const_add 1
  have h2 := (quad_hasDerivAt_inv_pow k h).comp w h1
  have h3 := h2.const_mul (a ^ k / n)
  have e : (fun w : ℂ => a ^ k / (n * (1 + a * w) ^ k)) =
      fun w => (a ^ k / n) * (((fun u : ℂ => (u ^ k)⁻¹) ∘ fun w : ℂ => 1 + a * w) w) := by
    funext w
    simp [div_eq_mul_inv]
    ring
  rw [e]
  convert h3 using 1
  simp [div_eq_mul_inv]
  ring

theorem hasDerivAt_fCDeriv (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : w ≠ 0)
    (hw' : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) : HasDerivAt (fCDeriv N σ) (fCDeriv2 N σ w) w := by
  have hs : HasDerivAt (fun w : ℂ => ∑ i, (σ i : ℂ) ^ 2 / ((N : ℂ) * (1 + (σ i : ℂ) * w) ^ 2))
      (∑ i, -(((2 : ℕ) : ℂ) * ((σ i : ℂ) ^ (2 + 1) /
        ((N : ℂ) * (1 + (σ i : ℂ) * w) ^ (2 + 1))))) w :=
    HasDerivAt.fun_sum fun i _ => quad_hasDerivAt_term 2 (σ i : ℂ) (N : ℂ) (hw' i)
  have h := (quad_hasDerivAt_inv_pow 2 hw).sub hs
  unfold fCDeriv fCDeriv2
  convert h using 1
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  push_cast
  ring

theorem hasDerivAt_fCDeriv2 (N : ℕ) (σ : Fin M → ℝ) {w : ℂ} (hw : w ≠ 0)
    (hw' : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) : HasDerivAt (fCDeriv2 N σ) (fCDeriv3 N σ w) w := by
  have hs : HasDerivAt (fun w : ℂ => ∑ i, (σ i : ℂ) ^ 3 / ((N : ℂ) * (1 + (σ i : ℂ) * w) ^ 3))
      (∑ i, -(((3 : ℕ) : ℂ) * ((σ i : ℂ) ^ (3 + 1) /
        ((N : ℂ) * (1 + (σ i : ℂ) * w) ^ (3 + 1))))) w :=
    HasDerivAt.fun_sum fun i _ => quad_hasDerivAt_term 3 (σ i : ℂ) (N : ℂ) (hw' i)
  have h := ((quad_hasDerivAt_inv_pow 3 hw).const_mul (-2 : ℂ)).add (hs.const_mul (2 : ℂ))
  unfold fCDeriv2 fCDeriv3
  convert h using 1
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  push_cast
  ring

theorem fCDeriv_ofReal (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : fCDeriv N σ x = fR1 N σ x := by
  unfold fCDeriv fR1
  push_cast
  rfl

theorem fCDeriv2_ofReal (N : ℕ) (σ : Fin M → ℝ) (x : ℝ) : fCDeriv2 N σ x = fR2 N σ x := by
  unfold fCDeriv2 fR2
  push_cast
  rfl

/-! ## The quadratic equation (quadr_edge), (def_al_be), (im_def_m) -/

/-- `α` of (def_al_be). -/
def alphaCoef (N : ℕ) (σ : Fin M → ℝ) (u m : ℂ) : ℂ :=
  -∑ i, m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))

/-- `β` of (def_al_be). -/
def betaCoef (N : ℕ) (σ : Fin M → ℝ) (m : ℂ) : ℂ :=
  1 - ∑ i, m ^ 2 * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2)

private lemma quad_term_identity (a n u m : ℂ) (hm : m ≠ 0)
    (hu' : 1 + a * u ≠ 0) (hm' : 1 + a * m ≠ 0) :
    u * m * (a / (n * (1 + a * u)) - a / (n * (1 + a * m))) =
      -(m ^ 2 * a ^ 2 / (n * (1 + a * m) ^ 2)) * (u - m) -
        m * a ^ 2 / (n * (1 + a * m) ^ 2 * (1 + a * u)) * (u - m) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  · generalize hp : 1 + a * u = p at *
    generalize hq : 1 + a * m = q at *
    field_simp
    subst hp hq
    ring

/-- (quadr_edge): `u m (f(u) - f(m)) = β (u - m) + α (u - m)²`. -/
theorem quadr_edge (N : ℕ) (σ : Fin M → ℝ) {u m : ℂ} (hu : u ≠ 0) (hm : m ≠ 0)
    (hu' : ∀ i, 1 + (σ i : ℂ) * u ≠ 0) (hm' : ∀ i, 1 + (σ i : ℂ) * m ≠ 0) :
    u * m * (fC N σ u - fC N σ m) =
      betaCoef N σ m * (u - m) + alphaCoef N σ u m * (u - m) ^ 2 := by
  have hsum : u * m * (∑ i, (σ i : ℂ) / (N * (1 + σ i * u)) -
      ∑ i, (σ i : ℂ) / (N * (1 + σ i * m))) =
      -(∑ i, m ^ 2 * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2)) * (u - m) -
        (∑ i, m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))) * (u - m) ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_congr rfl fun i _ => quad_term_identity (σ i : ℂ) (N : ℂ) u m hm (hu' i) (hm' i),
      Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib]
  unfold fC betaCoef alphaCoef
  have h0 : u * m * (-u⁻¹ - -m⁻¹) = u - m := by
    field_simp
    ring
  calc u * m * (-u⁻¹ + ∑ i, (σ i : ℂ) / (N * (1 + σ i * u)) -
        (-m⁻¹ + ∑ i, (σ i : ℂ) / (N * (1 + σ i * m))))
      = u * m * (-u⁻¹ - -m⁻¹) + u * m * (∑ i, (σ i : ℂ) / (N * (1 + σ i * u)) -
        ∑ i, (σ i : ℂ) / (N * (1 + σ i * m))) := by ring
    _ = _ := by
      rw [h0, hsum]
      ring

/-- `β = m² f'(m)`. -/
theorem betaCoef_eq (N : ℕ) (σ : Fin M → ℝ) {m : ℂ} (hm : m ≠ 0) :
    betaCoef N σ m = m ^ 2 * fCDeriv N σ m := by
  unfold betaCoef fCDeriv
  rw [mul_sub, Finset.mul_sum]
  have h : m ^ 2 * (m ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hm)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Selection of the small root: if `β x + α x² = ε` and `2 C_α |x| ≤ |β|`, then
`|x| ≤ 2 |ε| / |β|`. -/
theorem root_dichotomy {α β ε x : ℂ} {Cα : ℝ} (hα : ‖α‖ ≤ Cα) (hβ : β ≠ 0)
    (hq : β * x + α * x ^ 2 = ε) (hx : 2 * Cα * ‖x‖ ≤ ‖β‖) : ‖x‖ ≤ 2 * ‖ε‖ / ‖β‖ := by
  have hβpos : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : ‖β * x‖ - ‖α * x ^ 2‖ ≤ ‖ε‖ := by
    rw [← hq]
    have := norm_sub_norm_le (β * x) (-(α * x ^ 2))
    rw [sub_neg_eq_add, norm_neg] at this
    exact this
  rw [norm_mul, norm_mul, norm_pow] at h1
  rw [le_div_iff₀ hβpos]
  have h2 : ‖α‖ * ‖x‖ ^ 2 ≤ Cα * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hα (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hx hx0]

/-- (im_def_m). -/
theorem im_def_m {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    ∑ i, σ i ^ 2 * ‖mFun N σ z‖ ^ 2 / (N * ‖1 + (σ i : ℂ) * mFun N σ z‖ ^ 2) =
      1 - ‖mFun N σ z‖ ^ 2 * z.im / (mFun N σ z).im := by
  obtain ⟨hm, hfm⟩ := mFun_spec N σ hσ hz
  have him := im_fC N σ (mFun N σ z)
  rw [hfm] at him
  set m := mFun N σ z with hmdef
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hn : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hS : ∑ i, σ i ^ 2 * ‖m‖ ^ 2 / (N * ‖1 + (σ i : ℂ) * m‖ ^ 2) =
      ‖m‖ ^ 2 * ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * m‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hS]
  set S := ∑ i, σ i ^ 2 / (N * ‖1 + (σ i : ℂ) * m‖ ^ 2)
  field_simp
  field_simp at him
  nlinarith [him]

/-- From (mz_reg) to (1+xm): `|1 + σ_i w| ≥ min(1/2, c/(2 C_m))` when `|w| ≤ C_m`. -/
def oneXmConst (c Cm : ℝ) : ℝ := min (1 / 2) (c / (2 * Cm))

theorem one_add_mul_ge_of_mz_reg {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {c Cm : ℝ} (hc : 0 < c)
    (hCm : 0 < Cm) {w : ℂ} (hw : ‖w‖ ≤ Cm) (hreg : ∀ s ∈ posVals σ, c ≤ ‖w + ((s⁻¹ : ℝ) : ℂ)‖) :
    ∀ i, oneXmConst c Cm ≤ ‖1 + (σ i : ℂ) * w‖ := by
  intro i
  have hmin1 : oneXmConst c Cm ≤ 1 / 2 := min_le_left _ _
  have hmin2 : oneXmConst c Cm ≤ c / (2 * Cm) := min_le_right _ _
  rcases (hσ i).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [Complex.ofReal_zero, zero_mul, add_zero, norm_one]
    linarith
  · by_cases hsmall : σ i * Cm ≤ 1 / 2
    · have h1 : ‖(σ i : ℂ) * w‖ ≤ 1 / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
        nlinarith [norm_nonneg w, mul_le_mul_of_nonneg_left hw hpos.le]
      have h2 : ‖(1 : ℂ)‖ - ‖(σ i : ℂ) * w‖ ≤ ‖1 + (σ i : ℂ) * w‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-((σ i : ℂ) * w))
        rwa [sub_neg_eq_add, norm_neg] at this
      rw [norm_one] at h2
      linarith
    · rw [not_le] at hsmall
      have hmem : σ i ∈ posVals σ := by
        simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨i, rfl⟩, hpos⟩
      have hr := hreg (σ i) hmem
      have heq : ‖1 + (σ i : ℂ) * w‖ = σ i * ‖w + (((σ i)⁻¹ : ℝ) : ℂ)‖ := by
        have hs : (σ i : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        have : 1 + (σ i : ℂ) * w = (σ i : ℂ) * (w + (((σ i)⁻¹ : ℝ) : ℂ)) := by
          push_cast
          field_simp
          ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      rw [heq]
      have h3 : c / (2 * Cm) ≤ σ i * c := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hr hpos.le]

/-! ## Instantiation at the MP instance, `N = 2`, `σ ≡ 1`, `z = i` -/

example : fCDeriv 2 (fun _ : Fin 1 => (1 : ℝ)) ((1 : ℝ) : ℂ) =
    fR1 2 (fun _ : Fin 1 => (1 : ℝ)) 1 :=
  fCDeriv_ofReal 2 _ 1

example : fCDeriv2 2 (fun _ : Fin 1 => (1 : ℝ)) ((1 : ℝ) : ℂ) =
    fR2 2 (fun _ : Fin 1 => (1 : ℝ)) 1 :=
  fCDeriv2_ofReal 2 _ 1

/-- `root_dichotomy` with explicit numbers: `α = 1`, `β = 2`, `x = 1/10`, `ε = β x + α x²`. -/
example : ‖(1 / 10 : ℂ)‖ ≤ 2 * ‖(2 * (1 / 10 : ℂ) + 1 * (1 / 10 : ℂ) ^ 2)‖ / ‖(2 : ℂ)‖ :=
  root_dichotomy (α := 1) (β := 2) (Cα := 1) (by simp) (by norm_num) rfl
    (by simp; norm_num)

/-- `root_dichotomy` at the MP instance; the two numerical facts about `α`, `β` at `m(i)` are
taken as hypotheses. -/
example
    (hβ : betaCoef 2 (fun _ : Fin 1 => (1 : ℝ)) (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I)
      ≠ 0)
    (hx : 2 * ‖alphaCoef 2 (fun _ : Fin 1 => (1 : ℝ))
        (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I + 1 / 10)
        (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I)‖ * ‖(1 / 10 : ℂ)‖ ≤
      ‖betaCoef 2 (fun _ : Fin 1 => (1 : ℝ))
        (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I)‖) :
    ‖(1 / 10 : ℂ)‖ ≤ 2 * ‖betaCoef 2 (fun _ : Fin 1 => (1 : ℝ))
        (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I) * (1 / 10) +
        alphaCoef 2 (fun _ : Fin 1 => (1 : ℝ))
          (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I + 1 / 10)
          (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I) * (1 / 10) ^ 2‖ /
      ‖betaCoef 2 (fun _ : Fin 1 => (1 : ℝ))
        (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I)‖ :=
  root_dichotomy le_rfl hβ rfl hx

example :
    ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i ^ 2 *
        ‖mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I‖ ^ 2 /
      ((2 : ℕ) * ‖1 + ((fun _ : Fin 1 => (1 : ℝ)) i : ℂ) *
        mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I‖ ^ 2) =
      1 - ‖mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I‖ ^ 2 * Complex.I.im /
        (mFun 2 (fun _ : Fin 1 => (1 : ℝ)) Complex.I).im :=
  im_def_m (N := 2) (fun _ => by norm_num) (by simp)

end Anisotropic
