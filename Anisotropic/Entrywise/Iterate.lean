module

public import Anisotropic.Entrywise.Control
public import Anisotropic.Density.Stability.Defs
public import Anisotropic.Density.Varrho

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The iteration sequence and the control functions `δ_k` -/

/-- `θ_0 = Φ^{1/4}`, `θ_{k+1} = Φ + (θ_k Φ)^{1/2}`. -/
def iterTheta : ℕ → ℝ → ℝ
  | 0, Φ => Φ ^ (1 / 4 : ℝ)
  | k + 1, Φ => Φ + √(iterTheta k Φ * Φ)

/-- `θ_k ≥ 0` on `[0, ∞)`. -/
private theorem iterTheta_nonneg (k : ℕ) {Φ : ℝ} (h : 0 ≤ Φ) : 0 ≤ iterTheta k Φ := by
  induction k with
  | zero => exact Real.rpow_nonneg h _
  | succ k _ => simp only [iterTheta]; positivity

/-- The exponent `e_k = 1 - (3/4) 2^{-k}` satisfies `(e_k + 1)/2 = e_{k+1}`. -/
private theorem iterExp_succ (k : ℕ) :
    (1 - 3 / 4 * ((1 : ℝ) / 2) ^ k + 1) * (1 / 2) = 1 - 3 / 4 * ((1 : ℝ) / 2) ^ (k + 1) := by
  rw [pow_succ]; ring

theorem iterTheta_le (k : ℕ) {Φ : ℝ} (h0 : 0 ≤ Φ) (h1 : Φ ≤ 1) :
    iterTheta k Φ ≤ 3 * Φ ^ (1 - 3 / 4 * ((1 : ℝ) / 2) ^ k) := by
  induction k with
  | zero =>
    have e : (1 - 3 / 4 * ((1 : ℝ) / 2) ^ 0) = 1 / 4 := by norm_num
    rw [e]
    have : 0 ≤ Φ ^ (1 / 4 : ℝ) := Real.rpow_nonneg h0 _
    simp only [iterTheta]
    linarith
  | succ k ih =>
    set e : ℝ := 1 - 3 / 4 * ((1 : ℝ) / 2) ^ k with he
    set e' : ℝ := 1 - 3 / 4 * ((1 : ℝ) / 2) ^ (k + 1) with he'
    have hpow : ((1 : ℝ) / 2) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpow0 : 0 < ((1 : ℝ) / 2) ^ k := by positivity
    have hpow' : ((1 : ℝ) / 2) ^ (k + 1) = ((1 : ℝ) / 2) ^ k * (1 / 2) := pow_succ _ _
    have he1 : 0 < e + 1 := by rw [he]; linarith
    have he'1 : e' ≤ 1 := by rw [he']; rw [hpow']; nlinarith
    have he'0 : 0 < e' := by rw [he']; rw [hpow']; nlinarith
    have hee : (e + 1) * (1 / 2) = e' := iterExp_succ k
    have hΦe : 0 ≤ Φ ^ e := Real.rpow_nonneg h0 _
    -- `θ_k Φ ≤ 3 Φ^{e+1}`
    have h2 : iterTheta k Φ * Φ ≤ 3 * Φ ^ (e + 1) := by
      rw [Real.rpow_add' h0 he1.ne', Real.rpow_one]
      calc iterTheta k Φ * Φ ≤ (3 * Φ ^ e) * Φ := mul_le_mul_of_nonneg_right ih h0
        _ = 3 * (Φ ^ e * Φ) := by ring
    have h3 : √(iterTheta k Φ * Φ) ≤ 2 * Φ ^ e' := by
      have h4 : √(iterTheta k Φ * Φ) ≤ √(3 * Φ ^ (e + 1)) := Real.sqrt_le_sqrt h2
      have h5 : √(3 * Φ ^ (e + 1)) = √3 * Φ ^ e' := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (Φ ^ (e + 1)),
          ← Real.rpow_mul h0, ← hee, mul_comm (e + 1) (1 / 2)]
      have h6 : √3 ≤ 2 := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have h7 : 0 ≤ Φ ^ e' := Real.rpow_nonneg h0 _
      calc √(iterTheta k Φ * Φ) ≤ √3 * Φ ^ e' := h5 ▸ h4
        _ ≤ 2 * Φ ^ e' := mul_le_mul_of_nonneg_right h6 h7
    have h8 : Φ ≤ Φ ^ e' := by
      rcases h0.eq_or_lt with h | h
      · rw [← h, Real.zero_rpow he'0.ne']
      · calc Φ = Φ ^ (1 : ℝ) := (Real.rpow_one Φ).symm
          _ ≤ Φ ^ e' := Real.rpow_le_rpow_of_exponent_ge h h1 he'1
    change Φ + √(iterTheta k Φ * Φ) ≤ 3 * Φ ^ e'
    linarith

theorem iterTheta_mono (k : ℕ) : MonotoneOn (iterTheta k) (Set.Ici 0) := by
  induction k with
  | zero =>
    intro a ha b _ hab
    exact Real.rpow_le_rpow ha hab (by norm_num)
  | succ k ih =>
    intro a ha b hb hab
    have ha' : 0 ≤ a := ha
    have hb' : 0 ≤ b := hb
    have h1 : iterTheta k a * a ≤ iterTheta k b * b :=
      mul_le_mul (ih ha hb hab) hab ha' (iterTheta_nonneg k hb')
    change a + √(iterTheta k a * a) ≤ b + √(iterTheta k b * b)
    linarith [Real.sqrt_le_sqrt h1]

/-- `√(xΦ)/Φ = √(x/Φ)` for `Φ > 0`. -/
private theorem iter_sqrt_mul_div {x Φ : ℝ} (hx : 0 ≤ x) (hΦ : 0 < Φ) :
    √(x * Φ) / Φ = √(x / Φ) := by
  have e : x / Φ = (x * Φ) / Φ ^ 2 := by field_simp
  rw [e, Real.sqrt_div (mul_nonneg hx hΦ.le), Real.sqrt_sq hΦ.le]

/-- `θ_k(Φ)/Φ` is nonincreasing on `(0, ∞)`. -/
private theorem iterTheta_div_anti (k : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    iterTheta k b / b ≤ iterTheta k a / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  induction k with
  | zero =>
    simp only [iterTheta]
    rw [← Real.rpow_sub_one hb.ne', ← Real.rpow_sub_one ha.ne']
    exact Real.rpow_le_rpow_of_nonpos ha hab (by norm_num)
  | succ k ih =>
    simp only [iterTheta]
    rw [add_div, add_div, div_self hb.ne', div_self ha.ne',
      iter_sqrt_mul_div (iterTheta_nonneg k hb.le) hb,
      iter_sqrt_mul_div (iterTheta_nonneg k ha.le) ha]
    linarith [Real.sqrt_le_sqrt ih]

/-- `Im m(z)/Im z` as a mean of the Poisson-type kernel. -/
private theorem iter_im_div_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ} (hz : 0 < z.im) :
    (resolventTransform μ z).im / z.im =
      ∫ x : ℝ, 1 / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
    refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable
    · rw [norm_inv]
      refine inv_anti₀ hz ?_
      have h := Complex.abs_im_le_norm ((x : ℂ) - z)
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
      exact le_trans (le_abs_self _) h
  rw [resolventTransform_apply]
  simp_rw [show ∀ x : ℝ, resolvent z x = ((x : ℂ) - z)⁻¹ from fun x => by
    simp [resolvent, Ring.inverse_eq_inv']]
  have him : (∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ).im = ∫ x : ℝ, (((x : ℂ) - z)⁻¹).im ∂μ := by
    have := integral_im (𝕜 := ℂ) hint
    simpa using this.symm
  rw [him, ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hn : (x - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by
    have : 0 < z.im ^ 2 := by positivity
    positivity
  simp only [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg,
    Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re]
  field_simp

/-- The kernel `x ↦ 1/((x - E)² + η²)` is integrable against a probability measure. -/
private theorem iter_integrable_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ] (E : ℝ) {η : ℝ}
    (hη : 0 < η) : Integrable (fun x : ℝ => 1 / ((x - E) ^ 2 + η ^ 2)) μ := by
  have hpos : ∀ x : ℝ, 0 < (x - E) ^ 2 + η ^ 2 := fun x => by positivity
  refine Integrable.of_bound ?_ ((η ^ 2)⁻¹) (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.div (by fun_prop) fun x => (hpos x).ne'
  · rw [Real.norm_of_nonneg (by have := hpos x; positivity), ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg (x - E)])

/-- `|θ(a)a - θ(b)b| ≤ 6 |a - b|` on `(0, 1]`, for `θ` monotone, nonnegative, bounded by `3`
with `θ(Φ)/Φ` nonincreasing. -/
private theorem iter_g_lip {θ : ℝ → ℝ} (hmono : MonotoneOn θ (Set.Ici 0))
    (hnn : ∀ Φ, 0 ≤ Φ → 0 ≤ θ Φ) (h3 : ∀ Φ, 0 ≤ Φ → Φ ≤ 1 → θ Φ ≤ 3)
    (hratio : ∀ a b : ℝ, 0 < a → a ≤ b → θ b / b ≤ θ a / a) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) : |θ a * a - θ b * b| ≤ 6 * |a - b| := by
  have key : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1 →
      0 ≤ θ b * b - θ a * a ∧ θ b * b - θ a * a ≤ 6 * (b - a) := by
    intro a b ha hab hb1
    have hb : 0 < b := lt_of_lt_of_le ha hab
    refine ⟨?_, ?_⟩
    · have h1 : θ a ≤ θ b := hmono (Set.mem_Ici.2 ha.le) (Set.mem_Ici.2 hb.le) hab
      have h2 := hnn b hb.le
      nlinarith
    · have hr := hratio a b ha hab
      rw [div_le_div_iff₀ hb ha] at hr
      have hT0 := hnn b hb.le
      have hT3 := h3 b hb.le hb1
      have h4 : (θ b * b - θ a * a) * b ≤ 6 * (b - a) * b := by
        nlinarith [mul_nonneg hT0 (sub_nonneg.2 hab), mul_nonneg (sub_nonneg.2 hab) hb.le,
          mul_nonneg (sub_nonneg.2 hab) ha.le, mul_nonneg hT0 ha.le]
      exact le_of_mul_le_mul_right h4 hb
  rcases le_total a b with hab | hab
  · obtain ⟨k1, k2⟩ := key a b ha hab hb1
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨k1, k2⟩ := key b a hb hab ha1
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- The numerical inequality closing the Lipschitz clause. -/
private theorem iter_arith {C n v : ℝ} (hC : 0 ≤ C) (hv : 2 ≤ v) (hn : 2 * (C + 6) ≤ n) :
    v ^ 2 * ((n / v ^ 4) * (n / v ^ 4)) * ((v ^ 4)⁻¹ + (C + 6) / n) ≤ n ^ 2 := by
  have hv0 : 0 < v := by linarith
  have hn0 : 0 < n := by linarith
  have e : v ^ 2 * ((n / v ^ 4) * (n / v ^ 4)) * ((v ^ 4)⁻¹ + (C + 6) / n) =
      n ^ 2 / v ^ 10 + (C + 6) * n / v ^ 6 := by
    field_simp
  rw [e]
  have h1 : (1 : ℝ) ≤ v ^ 6 := one_le_pow₀ (by linarith)
  have h2 : 2 ≤ v ^ 10 := by
    calc (2 : ℝ) ≤ v := hv
      _ = v ^ 1 := (pow_one v).symm
      _ ≤ v ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have a1 : n ^ 2 / v ^ 10 ≤ n ^ 2 / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
  have a2 : (C + 6) * n / v ^ 6 ≤ (C + 6) * n := div_le_self (by positivity) h1
  nlinarith

/-- `δ = N^s (Im m + θ(Φ)) Φ`. -/
def iterDelta (N : ℕ) (σ : Fin M → ℝ) (s : ℝ) (θ : ℝ → ℝ) (z : ℂ) : ℝ :=
  (N : ℝ) ^ s * ((mFun N σ z).im + θ (PhiN N z)) * PhiN N z

/-- `C_m > 0`. -/
private theorem iter_mBoundConst_pos {τ : ℝ} (hτ : 0 < τ) : 0 < mBoundConst τ := by
  unfold mBoundConst genPropConst
  exact div_pos (by positivity) (pow_pos (half_pos hτ) 4)

/-- The four clauses of admissibility for `δ = N^s (Im m + θ(Φ)) Φ`, for `θ` monotone and
nonnegative on `[0, ∞)`, bounded by `3` on `[0, 1]`, with `θ(Φ)/Φ` nonincreasing. -/
private theorem admissible_iterDelta_of {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) (hsτ : s ≤ τ / 2)
    {θ : ℝ → ℝ} (hmono : MonotoneOn θ (Set.Ici 0)) (hnn : ∀ Φ, 0 ≤ Φ → 0 ≤ θ Φ)
    (h3 : ∀ Φ, 0 ≤ Φ → Φ ≤ 1 → θ Φ ≤ 3)
    (hratio : ∀ a b : ℝ, 0 < a → a ≤ b → θ b / b ≤ θ a / a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ) (S : Set ℂ), DensityAssumptions τ N σ →
      S ⊆ specDomain τ N → AdmissibleDelta N S (iterDelta N σ s θ) := by
  set C := mBoundConst τ with hCdef
  have hC : 0 < C := iter_mBoundConst_pos hτ
  set B : ℝ := 4 * (C + 3) / τ + 2 * C + 14 with hB
  have hB1 : 4 * (C + 3) / τ ≤ B := by rw [hB]; linarith
  have hB2 : 2 * C + 14 ≤ B := by
    have : 0 ≤ 4 * (C + 3) / τ := by positivity
    rw [hB]; linarith
  refine ⟨⌈B ^ (4 / τ)⌉₊ + ⌈B⌉₊ + 2, fun N hN M σ S hD hS => ?_⟩
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hnB : B ≤ (N : ℝ) :=
    (Nat.le_ceil B).trans (by exact_mod_cast (by omega : ⌈B⌉₊ ≤ N))
  have hnB' : B ^ (4 / τ) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈B ^ (4 / τ)⌉₊ ≤ N))
  have hNpos : 0 < N := by omega
  have hσ : ∀ i, 0 ≤ σ i := hD.nonneg
  have := isProbabilityMeasure_varrho N σ hσ hNpos
  set n : ℝ := (N : ℝ) with hn
  have hn0 : 0 < n := by linarith
  set v : ℝ := n ^ (τ / 4) with hv
  have hvB : B ≤ v := by
    calc B = (B ^ (4 / τ)) ^ (τ / 4) := by
          rw [← Real.rpow_mul (by linarith)]
          have : 4 / τ * (τ / 4) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ v := Real.rpow_le_rpow (by positivity) hnB' (by positivity)
  have hv2 : 2 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hv4 : v ^ 4 = n ^ τ := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1; push_cast; ring
  have hv2' : v ^ 2 = n ^ (τ / 2) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1; push_cast; ring
  have hNs1 : 1 ≤ n ^ s := Real.one_le_rpow (by linarith) hs
  have hNs2 : n ^ s ≤ v ^ 2 := by
    rw [hv2']; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hsτ
  have hlog : Real.log n ≤ v / (τ / 4) := Real.log_le_rpow_div hn0.le (by positivity)
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hv4pos : 0 < v ^ 4 := by positivity
  have hQ1 : (v ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  -- facts at a point of `S`
  have pt : ∀ z ∈ S, 0 < z.im ∧ v ^ 4 / n ≤ z.im ∧ C⁻¹ * z.im ≤ (mFun N σ z).im ∧
      (mFun N σ z).im ≤ C := by
    intro z hz
    obtain ⟨h0, -, -, hη, -⟩ := hS hz
    obtain ⟨-, hm2, hm3⟩ := gen_prop_m_specDomain hD (hS hz)
    refine ⟨h0, ?_, hm3, (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm2)⟩
    have e : (N : ℝ) ^ (-1 + τ) = v ^ 4 / n := by
      rw [hv4, Real.rpow_add hn0, Real.rpow_neg_one]
      ring
    rw [← e]; exact hη
  have Phi_eq : ∀ z : ℂ, PhiN N z = (n * z.im)⁻¹ := fun z => rfl
  have Phi_pos : ∀ z ∈ S, 0 < PhiN N z := fun z hz => by
    rw [Phi_eq]; have := (pt z hz).1; positivity
  have Phi_le : ∀ z ∈ S, PhiN N z ≤ (v ^ 4)⁻¹ := fun z hz => by
    rw [Phi_eq]
    obtain ⟨h0, h1, -, -⟩ := pt z hz
    refine inv_anti₀ hv4pos ?_
    calc v ^ 4 = n * (v ^ 4 / n) := by field_simp
      _ ≤ n * z.im := mul_le_mul_of_nonneg_left h1 hn0.le
  have Phi_le1 : ∀ z ∈ S, PhiN N z ≤ 1 := fun z hz => (Phi_le z hz).trans hQ1
  have delta_eq : ∀ z : ℂ, iterDelta N σ s θ z =
      n ^ s * ((mFun N σ z).im * PhiN N z + θ (PhiN N z) * PhiN N z) := fun z => by
    unfold iterDelta; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lower
    intro z hz
    obtain ⟨h0, h1, h2, h3'⟩ := pt z hz
    have hΦ := Phi_pos z hz
    have hT := hnn _ hΦ.le
    have hI : 0 < (mFun N σ z).im := lt_of_lt_of_le (by positivity) h2
    have hCn : C ≤ n := by linarith
    have h4 : (mFun N σ z).im * PhiN N z ≤ iterDelta N σ s θ z := by
      rw [delta_eq]
      have g1 : 0 ≤ θ (PhiN N z) * PhiN N z := mul_nonneg hT hΦ.le
      nlinarith [mul_nonneg (sub_nonneg.2 hNs1) (mul_pos hI hΦ).le,
        mul_nonneg (by linarith : 0 ≤ n ^ s) g1]
    have h5 : (n ^ 2)⁻¹ ≤ (mFun N σ z).im * PhiN N z :=
      calc (n ^ 2)⁻¹ ≤ (C * n)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
        _ = C⁻¹ * z.im * (n * z.im)⁻¹ := by field_simp
        _ ≤ (mFun N σ z).im * PhiN N z := by
          rw [Phi_eq]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
    exact h5.trans h4
  · -- upper
    intro z hz
    obtain ⟨h0, h1, h2, h3'⟩ := pt z hz
    have hΦ := Phi_pos z hz
    have hT := hnn _ hΦ.le
    have hI : 0 < (mFun N σ z).im := lt_of_lt_of_le (by positivity) h2
    have hIC : (mFun N σ z).im + θ (PhiN N z) ≤ C + 3 :=
      add_le_add h3' (h3 _ hΦ.le (Phi_le1 z hz))
    have hδ : iterDelta N σ s θ z ≤ (C + 3) * (v ^ 2)⁻¹ := by
      unfold iterDelta
      calc n ^ s * ((mFun N σ z).im + θ (PhiN N z)) * PhiN N z
          ≤ v ^ 2 * (C + 3) * (v ^ 4)⁻¹ :=
            mul_le_mul (mul_le_mul hNs2 hIC (add_nonneg hI.le hT) (by positivity))
              (Phi_le z hz) hΦ.le (by positivity)
        _ = (C + 3) * (v ^ 2)⁻¹ := by field_simp
    rw [← one_div, le_div_iff₀ hlogpos]
    calc iterDelta N σ s θ z * Real.log n ≤ ((C + 3) * (v ^ 2)⁻¹) * (v / (τ / 4)) :=
          mul_le_mul hδ hlog hlogpos.le (by positivity)
      _ = (4 * (C + 3) / τ) / v := by field_simp
      _ ≤ 1 := (div_le_one hv0).2 (hB1.trans hvB)
  · -- Lipschitz
    intro z hz w hw
    obtain ⟨hzi, hz1, hz2, hz3⟩ := pt z hz
    obtain ⟨hwi, hw1, hw2, hw3⟩ := pt w hw
    have hx0 : 0 ≤ ‖z - w‖ := norm_nonneg _
    have hK0 : 0 < n / v ^ 4 := by positivity
    have hiz : z.im⁻¹ ≤ n / v ^ 4 := by
      rw [← inv_div]; exact inv_anti₀ (by positivity) hz1
    have hiw : w.im⁻¹ ≤ n / v ^ 4 := by
      rw [← inv_div]; exact inv_anti₀ (by positivity) hw1
    have hm : ‖mFun N σ z - mFun N σ w‖ ≤ ‖z - w‖ / (z.im * w.im) := by
      have := norm_resolventTransform_sub_le (varrho N σ) hzi hwi
      rwa [resolventTransform_varrho N σ hσ hNpos hzi,
        resolventTransform_varrho N σ hσ hNpos hwi] at this
    have hKK : 1 / (z.im * w.im) ≤ (n / v ^ 4) * (n / v ^ 4) := by
      rw [one_div, mul_inv]; exact mul_le_mul hiz hiw (by positivity) hK0.le
    have hIm : |(mFun N σ z).im - (mFun N σ w).im| ≤ ‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) :=
      calc |(mFun N σ z).im - (mFun N σ w).im| ≤ ‖mFun N σ z - mFun N σ w‖ := by
            simpa using Complex.abs_im_le_norm (mFun N σ z - mFun N σ w)
        _ ≤ ‖z - w‖ / (z.im * w.im) := hm
        _ = ‖z - w‖ * (1 / (z.im * w.im)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hKK hx0
    have hwz : |w.im - z.im| ≤ ‖z - w‖ := by
      have := Complex.abs_im_le_norm (w - z)
      rwa [Complex.sub_im, norm_sub_rev] at this
    have hΦd : |PhiN N z - PhiN N w| ≤ ‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n := by
      have e : PhiN N z - PhiN N w = (w.im - z.im) * (1 / (z.im * w.im)) / n := by
        rw [Phi_eq, Phi_eq]; field_simp
      rw [e, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 1 / (z.im * w.im)),
        abs_of_pos hn0]
      exact div_le_div_of_nonneg_right (mul_le_mul hwz hKK (by positivity) hx0) hn0.le
    have hIw : |(mFun N σ w).im| ≤ C := by
      rw [abs_of_nonneg (lt_of_lt_of_le (by positivity) hw2).le]; exact hw3
    have hΦz := Phi_pos z hz
    have hΦw := Phi_pos w hw
    have hA : |(mFun N σ z).im * PhiN N z - (mFun N σ w).im * PhiN N w| ≤
        ‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) * (v ^ 4)⁻¹ +
          C * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n) := by
      have e : (mFun N σ z).im * PhiN N z - (mFun N σ w).im * PhiN N w =
          ((mFun N σ z).im - (mFun N σ w).im) * PhiN N z +
            (mFun N σ w).im * (PhiN N z - PhiN N w) := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_pos hΦz]
        exact mul_le_mul hIm (Phi_le z hz) hΦz.le (by positivity)
      · rw [abs_mul]
        exact mul_le_mul hIw hΦd (abs_nonneg _) hC.le
    have hg : |θ (PhiN N z) * PhiN N z - θ (PhiN N w) * PhiN N w| ≤
        6 * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n) :=
      (iter_g_lip hmono hnn h3 hratio hΦz hΦw (Phi_le1 z hz) (Phi_le1 w hw)).trans
        (mul_le_mul_of_nonneg_left hΦd (by norm_num))
    rw [delta_eq, delta_eq, ← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ n ^ s)]
    have hsum : |((mFun N σ z).im * PhiN N z + θ (PhiN N z) * PhiN N z) -
        ((mFun N σ w).im * PhiN N w + θ (PhiN N w) * PhiN N w)| ≤
        ‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) * (v ^ 4)⁻¹ +
          C * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n) +
          6 * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n) := by
      have e : ((mFun N σ z).im * PhiN N z + θ (PhiN N z) * PhiN N z) -
          ((mFun N σ w).im * PhiN N w + θ (PhiN N w) * PhiN N w) =
          ((mFun N σ z).im * PhiN N z - (mFun N σ w).im * PhiN N w) +
            (θ (PhiN N z) * PhiN N z - θ (PhiN N w) * PhiN N w) := by ring
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add hA hg)
    calc n ^ s * |((mFun N σ z).im * PhiN N z + θ (PhiN N z) * PhiN N z) -
        ((mFun N σ w).im * PhiN N w + θ (PhiN N w) * PhiN N w)|
        ≤ v ^ 2 * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) * (v ^ 4)⁻¹ +
          C * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n) +
          6 * (‖z - w‖ * ((n / v ^ 4) * (n / v ^ 4)) / n)) :=
          mul_le_mul hNs2 hsum (abs_nonneg _) (by positivity)
      _ = ‖z - w‖ * (v ^ 2 * ((n / v ^ 4) * (n / v ^ 4)) * ((v ^ 4)⁻¹ + (C + 6) / n)) := by
          ring
      _ ≤ ‖z - w‖ * n ^ 2 :=
          mul_le_mul_of_nonneg_left (iter_arith hC.le hv2 (by linarith)) hx0
      _ = n ^ 2 * ‖z - w‖ := mul_comm _ _
  · -- antitone
    intro z hz w hw hre him
    obtain ⟨hzi, hz1, hz2, hz3⟩ := pt z hz
    obtain ⟨hwi, hw1, hw2, hw3⟩ := pt w hw
    have hIη : (mFun N σ w).im / w.im ≤ (mFun N σ z).im / z.im := by
      rw [← resolventTransform_varrho N σ hσ hNpos hwi,
        ← resolventTransform_varrho N σ hσ hNpos hzi,
        iter_im_div_eq _ hwi, iter_im_div_eq _ hzi, hre]
      refine integral_mono (iter_integrable_kernel _ _ hwi) (iter_integrable_kernel _ _ hzi) ?_
      intro x
      refine one_div_le_one_div_of_le (by positivity) ?_
      have := pow_le_pow_left₀ hzi.le him 2
      linarith
    have hA : ∀ y ∈ S, (mFun N σ y).im * PhiN N y = ((mFun N σ y).im / y.im) / n := by
      intro y hy
      have := (pt y hy).1
      rw [Phi_eq]; field_simp
    have hΦwz : PhiN N w ≤ PhiN N z := by
      rw [Phi_eq, Phi_eq]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left him hn0.le)
    have hΦw := Phi_pos w hw
    have hg : θ (PhiN N w) * PhiN N w ≤ θ (PhiN N z) * PhiN N z :=
      calc θ (PhiN N w) * PhiN N w ≤ θ (PhiN N z) * PhiN N w :=
            mul_le_mul_of_nonneg_right
              (hmono (Set.mem_Ici.2 hΦw.le) (Set.mem_Ici.2 (Phi_pos z hz).le) hΦwz) hΦw.le
        _ ≤ θ (PhiN N z) * PhiN N z :=
            mul_le_mul_of_nonneg_left hΦwz (hnn _ (Phi_pos z hz).le)
    rw [delta_eq, delta_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [hA z hz, hA w hw]
    have := div_le_div_of_nonneg_right hIη hn0.le
    linarith

theorem admissible_iterDelta {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) (hsτ : s ≤ τ / 2) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ) (S : Set ℂ), DensityAssumptions τ N σ →
      S ⊆ specDomain τ N → AdmissibleDelta N S (iterDelta N σ s (iterTheta k)) :=
  admissible_iterDelta_of hτ hs hsτ (iterTheta_mono k) (fun _ h => iterTheta_nonneg k h)
    (fun Φ h0 h1 => by
      refine (iterTheta_le k h0 h1).trans ?_
      have hpow : ((1 : ℝ) / 2) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have : Φ ^ (1 - 3 / 4 * ((1 : ℝ) / 2) ^ k) ≤ 1 :=
        Real.rpow_le_one h0 h1 (by linarith)
      linarith)
    fun _ _ ha hab => iterTheta_div_anti k ha hab

theorem admissible_strongDelta {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) (hsτ : s ≤ τ / 2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ) (S : Set ℂ), DensityAssumptions τ N σ →
      S ⊆ specDomain τ N → AdmissibleDelta N S (iterDelta N σ s fun Φ => Φ) :=
  admissible_iterDelta_of hτ hs hsτ (fun _ _ _ _ h => h) (fun _ h => h)
    (fun _ _ h1 => by linarith)
    fun a b ha hab => by
      rw [div_self (lt_of_lt_of_le ha hab).ne', div_self ha.ne']

/-! ## Checks -/

section Checks

example : iterTheta 1 (1 / 4) = 1 / 4 + √((1 / 4 : ℝ) ^ (1 / 4 : ℝ) * (1 / 4)) := rfl

/-- `θ_2(1/4) ≤ 3 (1/4)^{13/16}`. -/
example : iterTheta 2 (1 / 4) ≤ 3 * (1 / 4 : ℝ) ^ (1 - 3 / 4 * ((1 : ℝ) / 2) ^ 2) :=
  iterTheta_le 2 (by norm_num) (by norm_num)

/-- `θ_1(1/4) ≤ θ_1(1/2)`. -/
example : iterTheta 1 (1 / 4) ≤ iterTheta 1 (1 / 2) :=
  iterTheta_mono 1 (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2 (by norm_num)) (by norm_num)

end Checks

end Anisotropic
