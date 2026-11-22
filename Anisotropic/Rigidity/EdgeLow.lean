module

public import Anisotropic.Averaged.Defs
public import Anisotropic.Averaged.Main
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.Stability.Defs
public import Anisotropic.Density.Stability.Domains
public import Anisotropic.Density.Stability.EdgeSqRoot
public import Anisotropic.Density.Stability.EdgeStab
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.Endpoints.Main
public import Anisotropic.Endpoints.Regions
public import Anisotropic.Entrywise.Defs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Model
public import Anisotropic.Gaussian.Ensemble
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The edge law with the lower cutoff decoupled from the window (`stab_edge2_weak'`, `oneXm_edge'`, `edge_law'`, `LL_G_low`) -/

/-! ## The window `|E - a_k| ≤ τ''` at an edge regular at `τ`

The facts below depend on `z` only through `η > 0`, the window `|E - a_k| ≤ τ''` with
`τ'' ≤ τ'(τ)` and, in the step from `z + iN⁻⁵` to `z`, `η ≥ N⁻¹`. They hold on
`𝐃^e_k(τ₂, τ'', N)` for every `τ₂ ∈ (0, τ]`. -/

/-- `κ = |E - a_k|` for `|E - a_k| ≤ τ'' ≤ τ/2` at an edge regular at `τ` (§3.3). -/
private lemma edgeLow_kappa {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ τ / 2) {z : ℂ}
    (hE : |z.re - edgeVal N σ k| ≤ τ'') : kappa N σ z.re = |z.re - edgeVal N σ k| := by
  obtain ⟨hk1, hk2, -, hsep, -⟩ := hk
  have hmem : k ∈ Finset.Icc 1 (2 * numBands N σ) := Finset.mem_Icc.2 ⟨hk1, hk2⟩
  have : Nonempty (Finset.Icc 1 (2 * numBands N σ)) := ⟨⟨k, hmem⟩⟩
  unfold kappa
  refine le_antisymm ?_ ?_
  · refine ciInf_le ⟨0, ?_⟩ (⟨k, hmem⟩ : Finset.Icc 1 (2 * numBands N σ))
    rintro _ ⟨l, rfl⟩
    exact abs_nonneg _
  · refine le_ciInf fun l => ?_
    by_cases hl : (l : ℕ) = k
    · rw [hl]
    · obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.1 l.2
      have h1 := hsep l hl1 hl2 hl
      have h2 : |edgeVal N σ k - edgeVal N σ l| ≤
          |z.re - edgeVal N σ l| + |z.re - edgeVal N σ k| := by
        have := abs_sub (z.re - edgeVal N σ l) (z.re - edgeVal N σ k)
        rwa [show z.re - edgeVal N σ l - (z.re - edgeVal N σ k) =
          edgeVal N σ k - edgeVal N σ l by ring] at this
      linarith

/-! ### Elementary facts on the assumptions and the constants -/

/-- `DensityAssumptions` forces `0 < τ ≤ 1` and `N > 0`. -/
private lemma edgeLow_facts {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) :
    0 < τ ∧ τ ≤ 1 ∧ 0 < N := by
  have hτ := h.pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := h.phi_lower
      simp [phiRatio, h0] at this
      linarith
    · exact h0
  have hτ1 : τ ≤ 1 := by
    have h1 : τ ≤ τ⁻¹ := h.phi_lower.trans h.phi_upper
    by_contra hc
    exact absurd h1 (not_le.mpr ((inv_lt_one_of_one_lt₀ (not_le.mp hc)).trans (not_le.mp hc)))
  exact ⟨hτ, hτ1, hN⟩

/-- The constants of Lemma A.3 at `τ ∈ (0, 1]`: positivity, `ρ₁ ≤ c_x/2`, `ρ₁ ≤ τ/2`,
`τ' = c₂ ρ₁² / 32` and `τ' ≤ τ/2`. -/
private lemma edgeLow_consts {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < edgecx τ ∧ 0 < edgeCx τ ∧ 0 < edgec2 τ ∧ 0 < edgeC2 τ ∧ 0 < edgeRho1 τ ∧
      edgeRho1 τ ≤ edgeRho0 τ ∧ edgeRho1 τ ≤ edgecx τ / 2 ∧ edgeRho1 τ ≤ τ / 2 ∧
      0 < edgeTau' τ ∧ edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 ∧ edgeTau' τ ≤ τ / 2 := by
  have hs := Real.sqrt_pos.2 hτ
  have hcx : 0 < edgecx τ := by unfold edgecx; positivity
  have hCx : 0 < edgeCx τ := by unfold edgeCx; positivity
  have h2 : 0 < edgec2 τ := by unfold edgec2; positivity
  have hC2 : 0 < edgeC2 τ := by unfold edgeC2; positivity
  have h3 : 0 < edgeC3 τ := by unfold edgeC3; positivity
  have h0 : 0 < edgeRho0 τ := by unfold edgeRho0; positivity
  have h1 : 0 < edgeRho1 τ := by unfold edgeRho1; positivity
  have h10 : edgeRho1 τ ≤ edgeRho0 τ := min_le_left _ _
  have h1c : edgeRho1 τ ≤ edgecx τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_left (edgecx τ) τ]
  have h1τ : edgeRho1 τ ≤ τ / 2 := by
    refine h10.trans ?_
    unfold edgeRho0; linarith [min_le_right (edgecx τ) τ]
  have hc2τ : edgec2 τ ≤ τ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have heq : edgeTau' τ = edgec2 τ * edgeRho1 τ ^ 2 / 32 := by
    unfold edgeTau' edgeTau0; ring
  have ht : 0 < edgeTau' τ := by rw [heq]; positivity
  have htτ : edgeTau' τ ≤ τ / 2 := by
    rw [heq]
    have hsq : edgeRho1 τ ^ 2 ≤ (τ / 2) ^ 2 := pow_le_pow_left₀ h1.le h1τ 2
    have hmul : edgec2 τ * edgeRho1 τ ^ 2 ≤ τ ^ 3 / 4 * (τ / 2) ^ 2 :=
      mul_le_mul hc2τ hsq (sq_nonneg _) (by positivity)
    have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
    nlinarith
  exact ⟨hcx, hCx, h2, hC2, h1, h10, h1c, h1τ, ht, heq, htτ⟩

/-- The constants of Lemma A.5 at `τ ∈ (0, 1]` are positive. -/
private lemma edgeLow_consts2 {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < edgeCeps τ ∧ 0 < edgeCalpha τ ∧ 0 < edgecbeta τ ∧ 0 < edgecgap τ ∧
      0 < edgeCloc τ ∧ 0 < mBoundConst τ ∧ 0 < sqUpper τ := by
  obtain ⟨hcx, hCx, h2, hC2, h1, -, -, -, ht, -, -⟩ := edgeLow_consts hτ hτ1
  have he : 0 < edgeCeps τ := by unfold edgeCeps; positivity
  have ha : 0 < edgeCalpha τ := by unfold edgeCalpha; positivity
  have hb : 0 < edgecbeta τ := by unfold edgecbeta; positivity
  have hg : 0 < edgecgap τ := by unfold edgecgap; positivity
  have hl : 0 < edgeCloc τ := by unfold edgeCloc; positivity
  have hm : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
  have hu : 0 < sqUpper τ := by
    have : 0 < mBoundConst τ / √(edgeTau' τ) := by positivity
    exact this.trans_le ((le_max_right _ _).trans (le_max_left _ _))
  exact ⟨he, ha, hb, hg, hl, hm, hu⟩

/-- `a ≤ b` from `c/4 · a² ≤ X` with `b = 2 c^{-1/2} X^{1/2}`. -/
private lemma edgeLow_le_of_sq {a c X : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (h : c / 4 * a ^ 2 ≤ X) : a ≤ 2 / √c * √X := by
  have hX : 0 ≤ X := le_trans (by positivity) h
  have hsc := Real.sqrt_pos.2 hc
  have hb : 0 ≤ 2 / √c * √X := by positivity
  rw [← pow_le_pow_iff_left₀ ha hb two_ne_zero]
  rw [mul_pow, div_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hX]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

/-- Regularity of the edge away from the junk value: `|x_k + s⁻¹| ≥ τ` for `s ∈ posVals σ`. -/
private lemma edgeLow_reg {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) :
    ∀ s ∈ posVals σ, τ ≤ |xCrit N σ k + s⁻¹| := by
  have hfin : ¬ (k = 2 * numBands N σ ∧ yEdge N σ = 0) := by
    rintro ⟨hk', hy⟩
    have : edgeVal N σ k = 0 := by
      unfold edgeVal
      simp only [hk', ↓reduceIte, hy]
      simp [FChart]
    linarith [hk.2.2.1, h.pos]
  exact hk.2.2.2.2 hfin

/-- `|1 + s v| ≥ s τ / 2` for `s > 0` with `|x_k + s⁻¹| ≥ τ` and `|v - x_k| ≤ τ/2`. -/
private lemma edgeLow_one_add {τ s x : ℝ} {v : ℂ} (hs : 0 < s) (hreg : τ ≤ |x + s⁻¹|)
    (hv : ‖v - x‖ ≤ τ / 2) : s * τ / 2 ≤ ‖1 + (s : ℂ) * v‖ := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have e : 1 + (s : ℂ) * v = (s : ℂ) * (((x + s⁻¹ : ℝ) : ℂ) + (v - x)) := by
    push_cast
    rw [mul_add, mul_add, mul_inv_cancel₀ hs']
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have h1 : ‖((x + s⁻¹ : ℝ) : ℂ)‖ - ‖v - x‖ ≤ ‖((x + s⁻¹ : ℝ) : ℂ) + (v - x)‖ := by
    have := norm_sub_norm_le ((x + s⁻¹ : ℝ) : ℂ) (-(v - x))
    rwa [sub_neg_eq_add, norm_neg] at this
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  have : τ / 2 ≤ ‖((x + s⁻¹ : ℝ) : ℂ) + (v - x)‖ := by linarith
  calc s * τ / 2 = s * (τ / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hs.le

/-- Geometry of the window `|E - a_k| ≤ τ''` below `η = τ'`: `κ = |E - a_k| ≤ τ'`,
`κ + η ≤ √2 |z - a_k|`, `|z - a_k| ≤ κ + η < 2τ'`, and (z-a_taylor) for `m(z)`. -/
private lemma edgeLow_point {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hη0 : 0 < z.im) (hE : |z.re - edgeVal N σ k| ≤ τ'')
    (hη : z.im < edgeTau' τ) :
    kappa N σ z.re = |z.re - edgeVal N σ k| ∧ kappa N σ z.re ≤ edgeTau' τ ∧ 0 < z.im ∧
      kappa N σ z.re + z.im ≤ √2 * ‖z - edgeVal N σ k‖ ∧
      ‖z - edgeVal N σ k‖ ≤ kappa N σ z.re + z.im ∧
      kappa N σ z.re + z.im < 2 * edgeTau' τ ∧
      ‖mFun N σ z - xCrit N σ k‖ < edgeRho1 τ ∧ fC N σ (mFun N σ z) = z ∧
      edgec2 τ / 4 * ‖mFun N σ z - xCrit N σ k‖ ^ 2 ≤ ‖z - edgeVal N σ k‖ ∧
      ‖z - edgeVal N σ k‖ ≤ edgeC2 τ * ‖mFun N σ z - xCrit N σ k‖ ^ 2 := by
  obtain ⟨hτ, hτ1, -⟩ := edgeLow_facts h
  obtain ⟨-, -, -, -, -, -, -, -, ht, heq, htτ⟩ := edgeLow_consts hτ hτ1
  have hκ := edgeLow_kappa hk (hτ''.trans htτ) hE
  have hre : (z - edgeVal N σ k).re = z.re - edgeVal N σ k := by simp
  have him : (z - edgeVal N σ k).im = z.im := by simp
  have hup : ‖z - edgeVal N σ k‖ ≤ kappa N σ z.re + z.im := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z - edgeVal N σ k)
    rw [hre, him, abs_of_pos hη0] at h1
    rw [hκ]; exact h1
  have hlow : kappa N σ z.re + z.im ≤ √2 * ‖z - edgeVal N σ k‖ := by
    have hsq : ‖z - edgeVal N σ k‖ ^ 2 = (z.re - edgeVal N σ k) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    have hab : (z.re - edgeVal N σ k) ^ 2 = |z.re - edgeVal N σ k| ^ 2 := (sq_abs _).symm
    rw [hκ]
    have h0 : 0 ≤ |z.re - edgeVal N σ k| + z.im := by positivity
    have h2 : (|z.re - edgeVal N σ k| + z.im) ^ 2 ≤ (√2 * ‖z - edgeVal N σ k‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), hsq, hab]
      nlinarith [sq_nonneg (|z.re - edgeVal N σ k| - z.im)]
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 h2
  have hκle : kappa N σ z.re ≤ edgeTau' τ := by rw [hκ]; linarith
  have h2t : kappa N σ z.re + z.im < 2 * edgeTau' τ := by linarith
  have hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ := by
    have : edgeTau0 τ = 4 * edgeTau' τ := by unfold edgeTau'; ring
    rw [this]; linarith
  obtain ⟨l0, l1, l2, l3, -⟩ := z_a_taylor h hk hη0.le hza
  have hm : mExt N σ z = mFun N σ z := by simp [mExt, hη0]
  rw [hm] at l0 l1 l2 l3
  exact ⟨hκ, hκle, hη0, hlow, hup, h2t, l0, l1, l2, l3⟩

/-! ### (al_be_claim) and the thin-regime bound -/

/-- (al_be_claim) in the form used: for `|E - a_k| ≤ τ''`, `0 < η < τ'` and `u` in the Taylor disk,
`|α| ≤ C_α`, `|β| ≥ c_β √(κ + η)`, `|u m| ≤ C_ε`. -/
private lemma edgeLow_coef_bounds {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hη0 : 0 < z.im) (hE : |z.re - edgeVal N σ k| ≤ τ'')
    (hη : z.im < edgeTau' τ) {u : ℂ}
    (hu : ‖u - xCrit N σ k‖ ≤ edgeRho1 τ) :
    ‖alphaCoef N σ u (mFun N σ z)‖ ≤ edgeCalpha τ ∧
    edgecbeta τ * √(kappa N σ z.re + z.im) ≤ ‖betaCoef N σ (mFun N σ z)‖ ∧
    ‖u * mFun N σ z‖ ≤ edgeCeps τ := by
  obtain ⟨hτ, hτ1, hN⟩ := edgeLow_facts h
  obtain ⟨hcx, hCx, hc2, hC2, hρ1, -, hρc, hρτ, -, -, -⟩ := edgeLow_consts hτ hτ1
  obtain ⟨-, -, hη0, hlow, -, -, hmx, -, -, hzC⟩ := edgeLow_point h hk hτ'' hη0 hE hη
  set m := mFun N σ z with hmdef
  set x := xCrit N σ k with hxdef
  obtain ⟨hxlo, hxhi, -⟩ := xCrit_bounds h hk
  have hreg := edgeLow_reg h hk
  have hmC : ‖m‖ ≤ edgeCx τ + edgeRho1 τ := by
    have := norm_le_norm_add_norm_sub' m x
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    have : ‖m‖ ≤ |x| + ‖m - x‖ := by
      calc ‖m‖ = ‖(x : ℂ) + (m - x)‖ := by ring_nf
        _ ≤ ‖(x : ℂ)‖ + ‖m - x‖ := norm_add_le _ _
        _ = |x| + ‖m - x‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have huC : ‖u‖ ≤ edgeCx τ + edgeRho1 τ := by
    have : ‖u‖ ≤ |x| + ‖u - x‖ := by
      calc ‖u‖ = ‖(x : ℂ) + (u - x)‖ := by ring_nf
        _ ≤ ‖(x : ℂ)‖ + ‖u - x‖ := norm_add_le _ _
        _ = |x| + ‖u - x‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- `|α| ≤ C_α`
    set A := ‖m‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg _
    set c := 4 * τ⁻¹ ^ 2 * A * (1 + 2 * τ⁻¹ * A) with hc
    have hc0 : 0 ≤ c := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hterm : ∀ i, ‖m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))‖ ≤ c / N := by
      intro i
      rcases (h.nonneg i).eq_or_lt with h0 | hpos
      · rw [← h0]; simp only [Complex.ofReal_zero]; simp; positivity
      · have hs : σ i ∈ posVals σ := by
          simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨⟨i, rfl⟩, hpos⟩
        have hr := hreg (σ i) hs
        have hmτ : ‖m - x‖ ≤ τ / 2 := hmx.le.trans hρτ
        have huτ : ‖u - x‖ ≤ τ / 2 := hu.trans hρτ
        have hAm := edgeLow_one_add hpos hr hmτ
        have hBu := edgeLow_one_add hpos hr huτ
        set a := ‖1 + (σ i : ℂ) * m‖
        set b := ‖1 + (σ i : ℂ) * u‖
        have ha0 : 0 < a := lt_of_lt_of_le (by positivity) hAm
        have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hBu
        have h1 : 1 ≤ a * (1 + 2 * τ⁻¹ * A) := by
          have t1 : ‖(1 : ℂ)‖ ≤ a + ‖(σ i : ℂ) * m‖ := by
            have := norm_add_le (1 + (σ i : ℂ) * m) (-((σ i : ℂ) * m))
            rwa [add_neg_cancel_right, norm_neg] at this
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le] at t1
          have t2 : σ i ≤ 2 * τ⁻¹ * a := by
            rw [show 2 * τ⁻¹ * a = a / (τ / 2) by field_simp]
            rw [le_div_iff₀ (by positivity)]; linarith
          have t3 : σ i * A ≤ 2 * τ⁻¹ * a * A := mul_le_mul_of_nonneg_right t2 hA0
          nlinarith
        have e : ‖m * (σ i : ℂ) ^ 2 / (N * (1 + σ i * m) ^ 2 * (1 + σ i * u))‖ =
            A / N * (1 / a) * (σ i / a) * (σ i / b) := by
          simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_natCast,
            Real.norm_of_nonneg hpos.le]
          change A * σ i ^ 2 / (N * a ^ 2 * b) = A / N * (1 / a) * (σ i / a) * (σ i / b)
          field_simp
        rw [e]
        have f1 : 1 / a ≤ 1 + 2 * τ⁻¹ * A := by
          rw [div_le_iff₀ ha0]; linarith
        have f2 : σ i / a ≤ 2 * τ⁻¹ := by
          rw [div_le_iff₀ ha0]
          have : σ i * τ / 2 * (2 * τ⁻¹) = σ i := by field_simp
          have := mul_le_mul_of_nonneg_right hAm (by positivity : (0 : ℝ) ≤ 2 * τ⁻¹)
          linarith
        have f3 : σ i / b ≤ 2 * τ⁻¹ := by
          rw [div_le_iff₀ hb0]
          have : σ i * τ / 2 * (2 * τ⁻¹) = σ i := by field_simp
          have := mul_le_mul_of_nonneg_right hBu (by positivity : (0 : ℝ) ≤ 2 * τ⁻¹)
          linarith
        calc A / N * (1 / a) * (σ i / a) * (σ i / b)
            ≤ A / N * (1 + 2 * τ⁻¹ * A) * (2 * τ⁻¹) * (2 * τ⁻¹) := by gcongr
          _ = c / N := by rw [hc]; ring
    have hsum : ‖alphaCoef N σ u m‖ ≤ τ⁻¹ * c := by
      unfold alphaCoef
      rw [norm_neg]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hφ := h.phi_upper
      unfold phiRatio at hφ
      have e : (M : ℝ) * (c / N) = (M / N) * c := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hφ hc0
    refine hsum.trans ?_
    rw [hc]
    unfold edgeCalpha
    have hτi : 0 ≤ τ⁻¹ := by positivity
    calc τ⁻¹ * (4 * τ⁻¹ ^ 2 * A * (1 + 2 * τ⁻¹ * A))
        = 4 * τ⁻¹ ^ 3 * A * (1 + 2 * τ⁻¹ * A) := by ring
      _ ≤ _ := by gcongr
  · -- `|β| ≥ c_β √(κ + η)`
    have hm0 : m ≠ 0 := by
      intro h0
      have := mFun_spec N σ h.nonneg hη0
      rw [← hmdef, h0] at this
      simp at this
    rw [betaCoef_eq N σ hm0, norm_mul, norm_pow]
    have hd := (edge_disk_lower h hk hmx.le).2.2
    set r := ‖m - x‖
    have hmlow : edgecx τ / 2 ≤ ‖m‖ := by
      have : |x| ≤ ‖m‖ + r := by
        calc |x| = ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
          _ = ‖m - (m - x)‖ := by ring_nf
          _ ≤ ‖m‖ + r := norm_sub_le _ _
      linarith
    have hr : √(kappa N σ z.re + z.im) / √(√2 * edgeC2 τ) ≤ r := by
      have hK : kappa N σ z.re + z.im ≤ √2 * edgeC2 τ * r ^ 2 := by
        calc _ ≤ √2 * ‖z - edgeVal N σ k‖ := hlow
          _ ≤ √2 * (edgeC2 τ * r ^ 2) := mul_le_mul_of_nonneg_left hzC (by positivity)
          _ = _ := by ring
      have hpos : 0 < √(√2 * edgeC2 τ) := Real.sqrt_pos.2 (by positivity)
      rw [div_le_iff₀ hpos]
      calc √(kappa N σ z.re + z.im) ≤ √(√2 * edgeC2 τ * r ^ 2) := Real.sqrt_le_sqrt hK
        _ = r * √(√2 * edgeC2 τ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]; ring
    have e : edgecbeta τ * √(kappa N σ z.re + z.im) =
        (edgecx τ / 2) ^ 2 * (3 * edgec2 τ / 4 *
          (√(kappa N σ z.re + z.im) / √(√2 * edgeC2 τ))) := by
      unfold edgecbeta; ring
    rw [e]
    have hq0 : 0 ≤ 3 * edgec2 τ / 4 * (√(kappa N σ z.re + z.im) / √(√2 * edgeC2 τ)) := by
      positivity
    calc (edgecx τ / 2) ^ 2 * (3 * edgec2 τ / 4 *
          (√(kappa N σ z.re + z.im) / √(√2 * edgeC2 τ)))
        ≤ ‖m‖ ^ 2 * (3 * edgec2 τ / 4 * r) := by
          apply mul_le_mul (pow_le_pow_left₀ (by positivity) hmlow 2) _ hq0 (by positivity)
          exact mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ ‖m‖ ^ 2 * ‖fCDeriv N σ m‖ := mul_le_mul_of_nonneg_left hd (by positivity)
  · -- `|u m| ≤ C_ε`
    rw [norm_mul]
    unfold edgeCeps
    rw [sq]
    exact mul_le_mul huC hmC (norm_nonneg _) (by positivity)

/-- The thin-regime bound: for `u` in the Taylor disk,
`|u - m| ≤ C_loc (κ + η + |f(u) - z|)^{1/2}`. -/
private lemma edgeLow_local_bound {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hη0 : 0 < z.im) (hE : |z.re - edgeVal N σ k| ≤ τ'')
    (hη : z.im < edgeTau' τ) {u : ℂ}
    (hu : ‖u - xCrit N σ k‖ ≤ edgeRho1 τ) :
    ‖u - mFun N σ z‖ ≤ edgeCloc τ * √(kappa N σ z.re + z.im + ‖fC N σ u - z‖) := by
  obtain ⟨hτ, hτ1, -⟩ := edgeLow_facts h
  obtain ⟨-, -, hc2, -, -, -, -, -, -, -, -⟩ := edgeLow_consts hτ hτ1
  obtain ⟨-, -, hη0, -, hup, -, -, -, hmz, -⟩ := edgeLow_point h hk hτ'' hη0 hE hη
  set X := kappa N σ z.re + z.im + ‖fC N σ u - z‖
  have hκ0 := kappa_nonneg N σ z.re
  have hX1 : ‖z - edgeVal N σ k‖ ≤ X := by
    have := norm_nonneg (fC N σ u - z); linarith
  have hX2 : ‖fC N σ u - edgeVal N σ k‖ ≤ X := by
    calc ‖fC N σ u - edgeVal N σ k‖ = ‖(fC N σ u - z) + (z - edgeVal N σ k)‖ := by ring_nf
      _ ≤ ‖fC N σ u - z‖ + ‖z - edgeVal N σ k‖ := norm_add_le _ _
      _ ≤ X := by linarith
  have hu1 := edgeLow_le_of_sq (norm_nonneg _) hc2 ((edge_disk_lower h hk hu).1.trans hX2)
  have hm1 := edgeLow_le_of_sq (norm_nonneg _) hc2 (hmz.trans hX1)
  calc ‖u - mFun N σ z‖ = ‖(u - xCrit N σ k) - (mFun N σ z - xCrit N σ k)‖ := by ring_nf
    _ ≤ ‖u - xCrit N σ k‖ + ‖mFun N σ z - xCrit N σ k‖ := norm_sub_le _ _
    _ ≤ 2 / √(edgec2 τ) * √X + 2 / √(edgec2 τ) * √X := add_le_add hu1 hm1
    _ = edgeCloc τ * √X := by unfold edgeCloc; ring

/-! ### Arithmetic of the two-regime bound -/

/-- `C₀ g ≤ twoRegime C₀ C₁ K₀ κ η d D` when `C₀ ≤ C₁`. -/
private lemma edgeLow_ge {C₀ C₁ K₀ κ η d D : ℝ} (hC : C₀ ≤ C₁) (hd : 0 ≤ d) (hD : 0 ≤ D) :
    C₀ * (d / (D + √d)) ≤ twoRegime C₀ C₁ K₀ κ η d D := by
  have hq : 0 ≤ d / (D + √d) := div_nonneg hd (add_nonneg hD (Real.sqrt_nonneg d))
  unfold twoRegime
  split_ifs
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_right hC hq

/-- `d / (D + √d) ≤ √d`. -/
private lemma edgeLow_quot_le {d D : ℝ} (hd : 0 ≤ d) (hD : 0 ≤ D) : d / (D + √d) ≤ √d := by
  rcases hd.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hs := Real.sqrt_pos.2 hpos
    calc d / (D + √d) ≤ d / √d := div_le_div_of_nonneg_left hd hs (by linarith)
      _ = √d := Real.div_sqrt

/-- Exclusion of the large root in the weak form: `C₀ √δ + 2e ≤ c_gap s / 2` when
`K₀ δ < s²`, `(4 C₀ / c_gap)² ≤ K₀` and `8e ≤ c_gap s`. -/
private lemma edgeLow_excl_w {s d c C₀ e K : ℝ} (hs : 0 < s) (hd : 0 < d) (hc : 0 < c)
    (hC₀ : 0 ≤ C₀) (hK0 : 0 ≤ K) (hK : K * d < s ^ 2) (hKC : (4 * C₀ / c) ^ 2 ≤ K)
    (he : 8 * e ≤ c * s) : C₀ * √d + 2 * e ≤ c * s / 2 := by
  have h1 : √K * √d < s := by
    have h0 : 0 ≤ √K * √d := by positivity
    rw [← pow_lt_pow_iff_left₀ h0 hs.le two_ne_zero, mul_pow, Real.sq_sqrt hK0,
      Real.sq_sqrt hd.le]
    exact hK
  have h2 : 4 * C₀ / c ≤ √K := (Real.le_sqrt (by positivity) hK0).2 hKC
  have h3 : C₀ * √d ≤ c / 4 * (√K * √d) := by
    have : C₀ = c / 4 * (4 * C₀ / c) := by field_simp
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)) (by positivity)
  have h4 : c / 4 * (√K * √d) ≤ c / 4 * s := mul_le_mul_of_nonneg_left h1.le (by positivity)
  linarith

/-- The small root against the bound: `2 C_ε δ / (c_β s) ≤ C₀ δ / (D + √δ)` when
`D + √δ ≤ A s` and `2 C_ε A / c_β ≤ C₀`. -/
private lemma edgeLow_small {s d D A Ce cb C₀ : ℝ} (hs : 0 < s) (hd : 0 < d) (hD : 0 ≤ D)
    (hA : 0 < A) (hDA : D + √d ≤ A * s) (hcb : 0 < cb) (hCe : 0 ≤ Ce)
    (hC : 2 * Ce * A / cb ≤ C₀) : 2 * (Ce * d) / (cb * s) ≤ C₀ * (d / (D + √d)) := by
  have hsd : 0 < D + √d := add_pos_of_nonneg_of_pos hD (Real.sqrt_pos.2 hd)
  calc 2 * (Ce * d) / (cb * s) = 2 * Ce * A / cb * (d / (A * s)) := by field_simp
    _ ≤ C₀ * (d / (A * s)) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ C₀ * (d / (D + √d)) := by
      have hC0 : 0 ≤ C₀ := le_trans (by positivity) hC
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hd.le hsd hDA) hC0

/-- The thin regime against the bound: `C_loc √(X + δ) ≤ C₁ δ / (D + √δ)` when `X ≤ K₀ δ`,
`D ≤ A √δ` and `C_loc (K₀+1)^{1/2} (A + 1) ≤ C₁`. -/
private lemma edgeLow_thin {X d D A K Cl C₁ : ℝ} (hd : 0 < d) (hX : X ≤ K * d) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hDA : D ≤ A * √d) (hCl : 0 ≤ Cl) (hK : 0 ≤ K)
    (hC : Cl * √(K + 1) * (A + 1) ≤ C₁) : Cl * √(X + d) ≤ C₁ * (d / (D + √d)) := by
  have hsd := Real.sqrt_pos.2 hd
  have h1 : √(X + d) ≤ √(K + 1) * √d := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : √d / (A + 1) ≤ d / (D + √d) := by
    have e : √d / (A + 1) = d / ((A + 1) * √d) := by
      field_simp
      rw [Real.sq_sqrt hd.le]
    rw [e]
    exact div_le_div_of_nonneg_left hd.le (by positivity) (by linarith)
  have hC1 : 0 ≤ C₁ := le_trans (by positivity) hC
  calc Cl * √(X + d) ≤ Cl * (√(K + 1) * √d) := mul_le_mul_of_nonneg_left h1 hCl
    _ = Cl * √(K + 1) * (A + 1) * (√d / (A + 1)) := by field_simp
    _ ≤ C₁ * (√d / (A + 1)) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ C₁ * (d / (D + √d)) := mul_le_mul_of_nonneg_left h2 hC1

/-- Every lower bound on `N` and on `log N` holds for all large `N`. -/
private lemma edgeLow_eventually (A L : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, A ≤ (N : ℝ) ∧ L ≤ Real.log N := by
  refine ⟨⌈max A (Real.exp L)⌉₊, fun N hN => ?_⟩
  have h1 : max A (Real.exp L) ≤ (N : ℝ) := Nat.ceil_le.1 hN
  have hA := (le_max_left _ _).trans h1
  have hE := (le_max_right _ _).trans h1
  exact ⟨hA, (Real.le_log_iff_exp_le ((Real.exp_pos L).trans_le hE)).2 hE⟩

/-! ### The step from `z + iN⁻⁵` to `z` -/

/-- One step of the continuity argument below `η = τ'`: from `|u - m| ≤ P` at `z + iN⁻⁵` with
`P + 2N⁻³ ≤ ρ₁/2`, the drift bound `|x| ≤ P + 2N⁻³` at `z`, the selection of the small root of
(quadr_edge) when `|x| ≤ c_gap √(κ + η) / 2`, and the thin-regime bound. -/
private lemma edgeLow_core {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hη0 : 0 < z.im) (hE : |z.re - edgeVal N σ k| ≤ τ'')
    (hη : z.im < edgeTau' τ) (hηN : ((N : ℝ))⁻¹ ≤ z.im)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {d P : ℝ}
    (hw : ‖fC N σ (resolventTransform μ z) - z‖ ≤ d)
    (hprior : ‖resolventTransform μ (shiftUp N z) - mFun N σ (shiftUp N z)‖ ≤ P)
    (hP : P + 2 * ((N : ℝ) ^ 3)⁻¹ ≤ edgeRho1 τ / 2) :
    ‖resolventTransform μ z - mFun N σ z‖ ≤ P + 2 * ((N : ℝ) ^ 3)⁻¹ ∧
    (‖resolventTransform μ z - mFun N σ z‖ ≤ edgecgap τ * √(kappa N σ z.re + z.im) / 2 →
      ‖resolventTransform μ z - mFun N σ z‖ ≤
        2 * (edgeCeps τ * d) / (edgecbeta τ * √(kappa N σ z.re + z.im))) ∧
    ‖resolventTransform μ z - mFun N σ z‖ ≤ edgeCloc τ * √(kappa N σ z.re + z.im + d) := by
  obtain ⟨hτ, hτ1, hN⟩ := edgeLow_facts h
  obtain ⟨-, -, hc2, -, hρ1, hρ10, -, -, -, heq, -⟩ := edgeLow_consts hτ hτ1
  obtain ⟨he0, ha0, hb0, hg0, -, -, -⟩ := edgeLow_consts2 hτ hτ1
  obtain ⟨-, -, hη0, -, hup, h2t, -, hfm, hmz, -⟩ := edgeLow_point h hk hτ'' hη0 hE hη
  have hσ := h.nonneg
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set z' := shiftUp N z with hz'
  have hre' : z'.re = z.re := by
    rw [hz', shiftUp, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him' : z'.im = z.im + ((N : ℝ) ^ 5)⁻¹ := by
    rw [hz', shiftUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hN5 : 0 < ((N : ℝ) ^ 5)⁻¹ := by positivity
  have hη' : 0 < z'.im := by rw [him']; linarith
  have hdist : ‖z - z'‖ = ((N : ℝ) ^ 5)⁻¹ := by
    have : z - z' = -(((((N : ℝ) ^ 5)⁻¹ : ℝ) : ℂ) * Complex.I) := by rw [hz', shiftUp]; ring
    rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hN5.le]
  -- the Lipschitz bound `|v(z) - v(z')| ≤ N⁻⁵ / (η η') ≤ N⁻³`
  have hdrift : ‖z - z'‖ / (z.im * z'.im) ≤ ((N : ℝ) ^ 3)⁻¹ := by
    rw [hdist]
    have hηη : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ z.im * z'.im :=
      mul_le_mul hηN (by rw [him']; linarith) (by positivity) hη0.le
    calc ((N : ℝ) ^ 5)⁻¹ / (z.im * z'.im) ≤ ((N : ℝ) ^ 5)⁻¹ / ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) :=
          div_le_div_of_nonneg_left hN5.le (by positivity) hηη
      _ = ((N : ℝ) ^ 3)⁻¹ := by field_simp
  set u := resolventTransform μ z with hu
  have hu1 : ‖u - resolventTransform μ z'‖ ≤ ((N : ℝ) ^ 3)⁻¹ :=
    (norm_resolventTransform_sub_le μ hη0 hη').trans hdrift
  have hm1 : ‖mFun N σ z - mFun N σ z'‖ ≤ ((N : ℝ) ^ 3)⁻¹ := by
    have := isProbabilityMeasure_varrho N σ hσ hN
    have hL := norm_resolventTransform_sub_le (varrho N σ) hη0 hη'
    rw [resolventTransform_varrho N σ hσ hN hη0, resolventTransform_varrho N σ hσ hN hη'] at hL
    exact hL.trans hdrift
  have hx : ‖u - mFun N σ z‖ ≤ P + 2 * ((N : ℝ) ^ 3)⁻¹ := by
    calc ‖u - mFun N σ z‖ = ‖(u - resolventTransform μ z') +
          (resolventTransform μ z' - mFun N σ z') - (mFun N σ z - mFun N σ z')‖ := by ring_nf
      _ ≤ ‖u - resolventTransform μ z'‖ + ‖resolventTransform μ z' - mFun N σ z'‖ +
          ‖mFun N σ z - mFun N σ z'‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ P + 2 * ((N : ℝ) ^ 3)⁻¹ := by linarith
  -- localisation in the Taylor disk
  have hmx : ‖mFun N σ z - xCrit N σ k‖ ≤ edgeRho1 τ / 2 := by
    have h1 : edgec2 τ / 4 * ‖mFun N σ z - xCrit N σ k‖ ^ 2 ≤
        edgec2 τ / 4 * (edgeRho1 τ / 2) ^ 2 := by
      have : edgec2 τ / 4 * (edgeRho1 τ / 2) ^ 2 = 2 * edgeTau' τ := by rw [heq]; ring
      rw [this]; linarith
    have h2 := le_of_mul_le_mul_left h1 (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hux : ‖u - xCrit N σ k‖ ≤ edgeRho1 τ := by
    calc ‖u - xCrit N σ k‖ = ‖(u - mFun N σ z) + (mFun N σ z - xCrit N σ k)‖ := by ring_nf
      _ ≤ ‖u - mFun N σ z‖ + ‖mFun N σ z - xCrit N σ k‖ := norm_add_le _ _
      _ ≤ edgeRho1 τ := by linarith
  refine ⟨hx, fun hsmall => ?_, ?_⟩
  · -- selection of the small root
    obtain ⟨hα, hβ, hε⟩ := edgeLow_coef_bounds h hk hτ'' hη0 hE hη hux
    have hs0 : 0 < √(kappa N σ z.re + z.im) :=
      Real.sqrt_pos.2 (by linarith [kappa_nonneg N σ z.re])
    have hβpos : 0 < ‖betaCoef N σ (mFun N σ z)‖ :=
      lt_of_lt_of_le (by positivity) hβ
    have hβne : betaCoef N σ (mFun N σ z) ≠ 0 := norm_pos_iff.1 hβpos
    obtain ⟨hm0, hm', -⟩ := norm_fCDeriv3_le h hk ((le_of_lt (by linarith : edgeRho1 τ / 2 <
      edgeRho1 τ)).trans' hmx |>.trans hρ10)
    obtain ⟨hu0, hu', -⟩ := norm_fCDeriv3_le h hk (hux.trans hρ10)
    have hq := quadr_edge N σ hu0 hm0 hu' hm'
    rw [hfm] at hq
    have h2 : 2 * edgeCalpha τ * ‖u - mFun N σ z‖ ≤ ‖betaCoef N σ (mFun N σ z)‖ := by
      have e : edgeCalpha τ * edgecgap τ = edgecbeta τ := by
        unfold edgecgap; field_simp
      calc 2 * edgeCalpha τ * ‖u - mFun N σ z‖
          ≤ 2 * edgeCalpha τ * (edgecgap τ * √(kappa N σ z.re + z.im) / 2) :=
            mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = edgecbeta τ * √(kappa N σ z.re + z.im) := by rw [← e]; ring
        _ ≤ _ := hβ
    have hr := root_dichotomy hα hβne hq.symm h2
    have hεb : ‖u * mFun N σ z * (fC N σ u - z)‖ ≤ edgeCeps τ * d := by
      rw [norm_mul]
      exact mul_le_mul hε hw (norm_nonneg _) he0.le
    have hdn : 0 ≤ d := (norm_nonneg _).trans hw
    refine hr.trans ?_
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) hβ
  · -- the thin-regime bound
    have hl := edgeLow_local_bound h hk hτ'' hη0 hE hη hux
    refine hl.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) ?_)
    unfold edgeCloc; positivity

/-! ### Lemma A.5 at a fixed `N` -/

/-- The conditions on `N` used below, for all large `N`: `N ≥ 2`, `(log N)⁻¹ ≤ τ'/2`,
`C₁ (log N)^{-1/2} ≤ ρ₁/4`, `2N⁻³ ≤ ρ₁/4` and `8N⁻³ ≤ c_gap N⁻²`. -/
private lemma edgeLow_Nfacts {τ C₁ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hC₁0 : 0 ≤ C₁) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (2 : ℝ) ≤ N ∧ (Real.log N)⁻¹ ≤ edgeTau' τ / 2 ∧
      C₁ * √((Real.log N)⁻¹) ≤ edgeRho1 τ / 4 ∧ 2 * ((N : ℝ) ^ 3)⁻¹ ≤ edgeRho1 τ / 4 ∧
      8 * ((N : ℝ) ^ 3)⁻¹ ≤ edgecgap τ * ((N : ℝ) ^ 2)⁻¹ := by
  obtain ⟨-, -, -, -, hρ1, -, -, -, ht, -, -⟩ := edgeLow_consts hτ0 hτ1
  obtain ⟨-, -, -, hg0, -, -, -⟩ := edgeLow_consts2 hτ0 hτ1
  obtain ⟨N₀, hN₀⟩ := edgeLow_eventually (max (max 2 (8 / edgecgap τ)) (8 / edgeRho1 τ))
    (max (2 / edgeTau' τ) ((4 * C₁ / edgeRho1 τ) ^ 2))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hNA, hNL⟩ := hN₀ N hN
  have hN2 : (2 : ℝ) ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hNA)
  have hNg : 8 / edgecgap τ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNA)
  have hNρ : 8 / edgeRho1 τ ≤ N := (le_max_right _ _).trans hNA
  have hL1 : 2 / edgeTau' τ ≤ Real.log N := (le_max_left _ _).trans hNL
  have hL2 : (4 * C₁ / edgeRho1 τ) ^ 2 ≤ Real.log N := (le_max_right _ _).trans hNL
  have hNr : (0 : ℝ) < N := by linarith
  have hlog1 : (Real.log N)⁻¹ ≤ edgeTau' τ / 2 := by
    have := inv_anti₀ (by positivity) hL1
    rwa [inv_div] at this
  have hlog2 : C₁ * √((Real.log N)⁻¹) ≤ edgeRho1 τ / 4 := by
    rcases hC₁0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; positivity
    · have h1 : (Real.log N)⁻¹ ≤ (edgeRho1 τ / (4 * C₁)) ^ 2 := by
        have := inv_anti₀ (by positivity) hL2
        rwa [← inv_pow, inv_div] at this
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_sq (by positivity)] at h2
      calc C₁ * √((Real.log N)⁻¹) ≤ C₁ * (edgeRho1 τ / (4 * C₁)) :=
            mul_le_mul_of_nonneg_left h2 hpos.le
        _ = edgeRho1 τ / 4 := by field_simp
  have hN3 : ((N : ℝ) ^ 3)⁻¹ ≤ (N : ℝ)⁻¹ := by
    apply inv_anti₀ hNr
    nlinarith [sq_nonneg (N : ℝ)]
  have he1 : 2 * ((N : ℝ) ^ 3)⁻¹ ≤ edgeRho1 τ / 4 := by
    have : (N : ℝ)⁻¹ ≤ edgeRho1 τ / 8 := by
      rw [inv_le_comm₀ hNr (by positivity), inv_div]; exact hNρ
    linarith
  have he2 : 8 * ((N : ℝ) ^ 3)⁻¹ ≤ edgecgap τ * ((N : ℝ) ^ 2)⁻¹ := by
    have : 8 * ((N : ℝ) ^ 3)⁻¹ = 8 / (N : ℝ) * ((N : ℝ) ^ 2)⁻¹ := by field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [div_le_iff₀ hNr]
    rw [div_le_iff₀ hg0] at hNg
    linarith
  exact ⟨hN2, hlog1, hlog2, he1, he2⟩

/-- `η ≥ N⁻¹` on `𝐃(τ₂, N)` for `τ₂ ≥ 0` and `N ≥ 1`. -/
private lemma edgeLow_im_ge {τ₂ : ℝ} {N : ℕ} {z : ℂ} (hτ₂ : 0 ≤ τ₂) (hN : 0 < N)
    (hz : z ∈ specDomain τ₂ N) : ((N : ℝ))⁻¹ ≤ z.im := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := hz.2.2.2.1
  have h2 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ₂) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_neg_one] at h2
  linarith

/-- (m_sq_root), upper bound, in the form used below `η = τ'`:
`Im m(z) ≤ |m(z) - x_k| ≤ 2 c₂^{-1/2} |z - a_k|^{1/2} ≤ C_sq √(κ + η)`. -/
private lemma edgeLow_im_le {τ τ'' : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ'' : τ'' ≤ edgeTau' τ)
    {z : ℂ} (hη0 : 0 < z.im) (hE : |z.re - edgeVal N σ k| ≤ τ'')
    (hη : z.im < edgeTau' τ) :
    (mFun N σ z).im ≤ sqUpper τ * √(kappa N σ z.re + z.im) := by
  obtain ⟨hτ, hτ1, -⟩ := edgeLow_facts h
  obtain ⟨-, -, hc2, -, -, -, -, -, -, -, -⟩ := edgeLow_consts hτ hτ1
  obtain ⟨-, -, -, -, hup, -, -, -, hmz, -⟩ := edgeLow_point h hk hτ'' hη0 hE hη
  have hsc := Real.sqrt_pos.2 hc2
  have hκ0 := kappa_nonneg N σ z.re
  have h1 : (mFun N σ z).im ≤ ‖mFun N σ z - xCrit N σ k‖ := by
    have := Complex.abs_im_le_norm (mFun N σ z - xCrit N σ k)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have h2 := edgeLow_le_of_sq (norm_nonneg _) hc2 (hmz.trans hup)
  have h3 : 2 / √(edgec2 τ) ≤ sqUpper τ := by
    have h4 : 2 / √(edgec2 τ) ≤ 6 * √2 / √(edgec2 τ) := by
      refine div_le_div_of_nonneg_right ?_ hsc.le
      have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
      linarith
    have h5 : 0 ≤ (√τ)⁻¹ / edgeTau' τ ^ 2 := by positivity
    have h6 : 6 * √2 / √(edgec2 τ) + (√τ)⁻¹ / edgeTau' τ ^ 2 ≤ sqUpper τ :=
      (le_max_left _ _).trans (le_max_left _ _)
    linarith
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)))

/-- `8 N⁻³ ≤ c √(κ + η)` below `η = 1`, from `√(κ + η) ≥ η ≥ N⁻¹` and `8 N⁻³ ≤ c N⁻²`. -/
private lemma edgeLow_he8 {κ c : ℝ} {N : ℕ} {z : ℂ} (hη0 : 0 < z.im)
    (hηN : ((N : ℝ))⁻¹ ≤ z.im) (hκ : 0 ≤ κ)
    (hη1 : z.im < 1) (hN2 : (2 : ℝ) ≤ N) (he2 : 8 * ((N : ℝ) ^ 3)⁻¹ ≤ c * ((N : ℝ) ^ 2)⁻¹)
    (hc : 0 < c) : 8 * ((N : ℝ) ^ 3)⁻¹ ≤ c * √(κ + z.im) := by
  have hNr : (0 : ℝ) < N := by linarith
  have hηs' : z.im ≤ √(κ + z.im) := by
    refine (Real.le_sqrt hη0.le (by linarith)).2 ?_
    have : z.im ^ 2 ≤ z.im := by nlinarith
    linarith
  have hN21 : ((N : ℝ) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ := by
    apply inv_anti₀ hNr
    nlinarith
  have := mul_le_mul_of_nonneg_left (hN21.trans (hηN.trans hηs')) hc.le
  linarith

/-- Stability on `𝐃^e_k(τ₂, τ'', N)`, `τ₂ ≤ τ`, at a fixed `N` satisfying the conditions of
`edgeLow_Nfacts`; `C₀ ≥ 4τ'^{-2}(C_m(τ₂) + 1)` and `C₀ ≥ 2 C_ε (C_sq + 1) / c_β`. -/
private lemma edgeLow_weak_step {τ τ₂ τ'' C₀ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) (hτ₂ : 0 < τ₂) (hτ₂τ : τ₂ ≤ τ)
    (hτ''le : τ'' ≤ edgeTau' τ)
    (hC₀a : 4 / edgeTau' τ ^ 2 * (mBoundConst τ₂ + 1) ≤ C₀)
    (hC₀b : 2 * edgeCeps τ * (sqUpper τ + 1) / edgecbeta τ ≤ C₀) (hN2 : (2 : ℝ) ≤ N)
    (hlog1 : (Real.log N)⁻¹ ≤ edgeTau' τ / 2)
    (hlog2 : edgeC1w τ C₀ * √((Real.log N)⁻¹) ≤ edgeRho1 τ / 4)
    (he1 : 2 * ((N : ℝ) ^ 3)⁻¹ ≤ edgeRho1 τ / 4)
    (he2 : 8 * ((N : ℝ) ^ 3)⁻¹ ≤ edgecgap τ * ((N : ℝ) ^ 2)⁻¹) :
    StableOn C₀ (edgeC1w τ C₀) (edgeK0w τ C₀) N σ (edgeDomain τ₂ τ'' N σ k) := by
  obtain ⟨hτ0, hτ1, hN0⟩ := edgeLow_facts h
  obtain ⟨-, -, -, -, hρ1, -, -, -, ht, -, htτ⟩ := edgeLow_consts hτ0 hτ1
  obtain ⟨he0, -, hb0, hg0, hl0, -, hu0⟩ := edgeLow_consts2 hτ0 hτ1
  have h₂ : DensityAssumptions τ₂ N σ := h.mono hτ₂ hτ₂τ
  have hm0 : 0 < mBoundConst τ₂ := by unfold mBoundConst genPropConst; positivity
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) hC₀a
  set C₁ := edgeC1w τ C₀ with hC₁
  set K₀ := edgeK0w τ C₀ with hK₀
  have hC₀C₁ : C₀ ≤ C₁ := le_max_left _ _
  have hC₁b : edgeCloc τ * √(K₀ + 1) * (sqUpper τ * √K₀ + 1) ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 ≤ C₁ := hC₀0.trans hC₀C₁
  have hK₀1 : 1 ≤ K₀ := le_max_left _ _
  have hKC : (4 * C₀ / edgecgap τ) ^ 2 ≤ K₀ := le_max_right _ _
  have hK₀0 : 0 ≤ K₀ := by linarith
  have hNr : (0 : ℝ) < N := by linarith
  have hσ := h.nonneg
  intro δ hδ μ hμ z hz hw hprior
  set u := resolventTransform μ z with hu
  set d := δ z with hd
  have hdl : ((N : ℝ) ^ 2)⁻¹ ≤ d := hδ.lower z hz
  have hdu : d ≤ (Real.log N)⁻¹ := hδ.upper z hz
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdl
  have hsd : C₁ * √d ≤ edgeRho1 τ / 4 :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdu) hC₁0).trans hlog2
  have hη0 : 0 < z.im := hz.1.1
  have hE : |z.re - edgeVal N σ k| ≤ τ'' := by
    obtain ⟨-, h1, h2⟩ := hz
    rw [abs_le]; constructor <;> linarith
  have hηN : ((N : ℝ))⁻¹ ≤ z.im := edgeLow_im_ge hτ₂.le hN0 hz.1
  have hκ0 := kappa_nonneg N σ z.re
  have hs0 : 0 < √(kappa N σ z.re + z.im) := Real.sqrt_pos.2 (by linarith)
  have him0 : 0 < (mFun N σ z).im := (mFun_spec N σ hσ hη0).1
  unfold weakBound
  by_cases hηs : z.im < edgeTau' τ
  · -- `η < τ'`
    have hη1 : z.im < 1 := by linarith
    have hP := hprior hη1
    have hz' : shiftUp N z ∈ edgeDomain τ₂ τ'' N σ k := by
      refine shiftUp_mem (spectralDomain_edgeDomain τ₂ τ'' N σ k) hz ?_
      have : ((N : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN2 5]
      have : (1 : ℝ) ≤ τ₂⁻¹ := one_le_inv₀ hτ₂ |>.2 (hτ₂τ.trans hτ1)
      linarith
    have hre' : (shiftUp N z).re = z.re := by
      rw [shiftUp, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have him' : (shiftUp N z).im = z.im + ((N : ℝ) ^ 5)⁻¹ := by
      rw [shiftUp, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hN5 : 0 < ((N : ℝ) ^ 5)⁻¹ := by positivity
    have hd'l : ((N : ℝ) ^ 2)⁻¹ ≤ δ (shiftUp N z) := hδ.lower _ hz'
    have hd'0 : 0 < δ (shiftUp N z) := lt_of_lt_of_le (by positivity) hd'l
    have hd'd : δ (shiftUp N z) ≤ d :=
      hδ.antitone z hz _ hz' hre' (by rw [him']; linarith)
    have him'0 : 0 < (mFun N σ (shiftUp N z)).im :=
      (mFun_spec N σ hσ (by rw [him']; linarith)).1
    have hsd' : √(δ (shiftUp N z)) ≤ √d := Real.sqrt_le_sqrt hd'd
    have hB' : weakBound C₀ C₁ K₀ N σ δ (shiftUp N z) ≤ C₁ * √d := by
      unfold weakBound
      refine (twoRegime_le hC₀C₁ hd'0.le him'0.le).trans ?_
      exact mul_le_mul_of_nonneg_left ((edgeLow_quot_le hd'0.le him'0.le).trans hsd') hC₁0
    obtain ⟨hx, hsmall, hthin⟩ := edgeLow_core h hk hτ''le hη0 hE hηs hηN μ hw hP
      (by linarith)
    have hImm := edgeLow_im_le h hk hτ''le hη0 hE hηs
    by_cases hreg : K₀ * d < kappa N σ z.re + z.im
    · -- thick regime: `z + iN⁻⁵` is thick as well
      have hreg' : K₀ * δ (shiftUp N z) < kappa N σ (shiftUp N z).re + (shiftUp N z).im := by
        rw [hre', him']
        have : K₀ * δ (shiftUp N z) ≤ K₀ * d := mul_le_mul_of_nonneg_left hd'd hK₀0
        linarith
      have hB'0 : weakBound C₀ C₁ K₀ N σ δ (shiftUp N z) ≤ C₀ * √d := by
        unfold weakBound twoRegime
        simp only [hreg', ↓reduceIte]
        exact mul_le_mul_of_nonneg_left ((edgeLow_quot_le hd'0.le him'0.le).trans hsd') hC₀0
      have hB : twoRegime C₀ C₁ K₀ (kappa N σ z.re) z.im d (mFun N σ z).im =
          C₀ * (d / ((mFun N σ z).im + √d)) := by
        unfold twoRegime; simp only [hreg, ↓reduceIte]
      rw [hB]
      have hsq : √(kappa N σ z.re + z.im) ^ 2 = kappa N σ z.re + z.im :=
        Real.sq_sqrt (by linarith)
      have hregs : K₀ * d < √(kappa N σ z.re + z.im) ^ 2 := by rw [hsq]; exact hreg
      have he8 := edgeLow_he8 hη0 hηN hκ0 hη1 hN2 he2 hg0
      have hexcl := edgeLow_excl_w hs0 hd0 hg0 hC₀0 hK₀0 hregs hKC he8
      have h1 := hsmall (hx.trans (by linarith))
      refine h1.trans (edgeLow_small hs0 hd0 him0.le (by linarith : (0 : ℝ) < sqUpper τ + 1)
        ?_ hb0 he0.le hC₀b)
      have hdK : d ≤ K₀ * d := le_mul_of_one_le_left hd0.le hK₀1
      have : √d < √(kappa N σ z.re + z.im) :=
        Real.sqrt_lt_sqrt hd0.le (lt_of_le_of_lt hdK hreg)
      linarith
    · -- thin regime
      have hB : twoRegime C₀ C₁ K₀ (kappa N σ z.re) z.im d (mFun N σ z).im =
          C₁ * (d / ((mFun N σ z).im + √d)) := by
        unfold twoRegime; simp only [hreg, ↓reduceIte]
      rw [hB]
      have hX : kappa N σ z.re + z.im ≤ K₀ * d := not_lt.1 hreg
      have hDA : (mFun N σ z).im ≤ sqUpper τ * √K₀ * √d := by
        have : √(kappa N σ z.re + z.im) ≤ √K₀ * √d := by
          rw [← Real.sqrt_mul hK₀0]; exact Real.sqrt_le_sqrt hX
        calc (mFun N σ z).im ≤ sqUpper τ * √(kappa N σ z.re + z.im) := hImm
          _ ≤ sqUpper τ * (√K₀ * √d) := mul_le_mul_of_nonneg_left this hu0.le
          _ = sqUpper τ * √K₀ * √d := by ring
      exact hthin.trans (edgeLow_thin hd0 hX him0.le (by positivity) hDA hl0.le hK₀0 hC₁b)
  · -- `η ≥ τ'`
    have hηge : edgeTau' τ ≤ z.im := not_lt.1 hηs
    have hx : ‖u - mFun N σ z‖ ≤ 2 * d / edgeTau' τ ^ 2 := by
      have huim := im_resolventTransform_pos μ hη0
      have h1 := norm_sub_mFun_le_of_im_ge hσ hN0 ht hηge huim (hw.trans (hdu.trans hlog1))
      exact h1.trans (by gcongr)
    have hmC : (mFun N σ z).im ≤ mBoundConst τ₂ :=
      (Complex.im_le_norm _).trans (gen_prop_m_specDomain h₂ hz.1).2.1
    have hden : (mFun N σ z).im + √d ≤ mBoundConst τ₂ + 1 := by
      have h2 : √d ≤ 1 := Real.sqrt_le_one.2 ((hdu.trans hlog1).trans (by
        have : edgeTau' τ ≤ 1 := htτ.trans (by linarith)
        linarith))
      exact add_le_add hmC h2
    refine le_trans ?_ (edgeLow_ge hC₀C₁ hd0.le him0.le)
    have hsd' : 0 < (mFun N σ z).im + √d := by positivity
    calc ‖u - mFun N σ z‖ ≤ 2 * d / edgeTau' τ ^ 2 := hx
      _ ≤ 4 / edgeTau' τ ^ 2 * (mBoundConst τ₂ + 1) * (d / (mBoundConst τ₂ + 1)) := by
          have hp : 0 < mBoundConst τ₂ + 1 := by positivity
          rw [show 4 / edgeTau' τ ^ 2 * (mBoundConst τ₂ + 1) * (d / (mBoundConst τ₂ + 1)) =
            4 * d / edgeTau' τ ^ 2 by field_simp]
          gcongr; norm_num
      _ ≤ C₀ * (d / (mBoundConst τ₂ + 1)) := mul_le_mul_of_nonneg_right hC₀a (by positivity)
      _ ≤ C₀ * (d / ((mFun N σ z).im + √d)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hd0.le hsd' hden) hC₀0

/-! ## Lemma A.5 and (1+xm) at the domain parameter `τ₂ ≤ τ` -/

/-- Stability (Definition 5.4) on `𝐃^e_k(τ₂, τ'', N)` for an edge regular at `τ ≥ τ₂`, with the
window `τ'' ≤ τ'(τ)` independent of `τ₂`. -/
theorem stab_edge2_weak' (τ τ₂ τ'' : ℝ) (hτ₂ : 0 < τ₂) (hτ₂τ : τ₂ ≤ τ) (hτ'' : 0 < τ'')
    (hτ''le : τ'' ≤ edgeTau' τ) :
    ∃ C₀ C₁ K₀ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
      DensityAssumptions τ N σ → RegularEdge τ N σ k →
        StableOn C₀ C₁ K₀ N σ (edgeDomain τ₂ τ'' N σ k) := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨0, 0, 0, 0, fun N _ M σ k h _ => absurd (edgeLow_facts h).2.1 hτ1⟩
  have hτ0 : 0 < τ := lt_of_lt_of_le hτ₂ hτ₂τ
  obtain ⟨-, -, -, -, -, -, -, -, ht, -, -⟩ := edgeLow_consts hτ0 hτ1
  have hm0 : 0 < mBoundConst τ₂ := by unfold mBoundConst genPropConst; positivity
  set C₀ := max (4 / edgeTau' τ ^ 2 * (mBoundConst τ₂ + 1))
    (2 * edgeCeps τ * (sqUpper τ + 1) / edgecbeta τ) with hC₀
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (le_max_left _ _)
  obtain ⟨N₀, hN₀⟩ := edgeLow_Nfacts (C₁ := edgeC1w τ C₀) hτ0 hτ1
    (hC₀0.trans (le_max_left _ _))
  refine ⟨C₀, edgeC1w τ C₀, edgeK0w τ C₀, N₀, fun N hN M σ k h hk => ?_⟩
  obtain ⟨hN2, hlog1, hlog2, he1, he2⟩ := hN₀ N hN
  exact edgeLow_weak_step h hk hτ₂ hτ₂τ hτ''le (le_max_left _ _) (le_max_right _ _) hN2 hlog1
    hlog2 he1 he2

/-- (1+xm) on `𝐃^e_k(τ₂, τ'', N)` for an edge regular at `τ ≥ τ₂`, `τ'' ≤ τ'(τ)`. -/
theorem oneXm_edge' (τ τ₂ τ'' : ℝ) (hτ₂ : 0 < τ₂) (hτ₂τ : τ₂ ≤ τ) (hτ'' : 0 < τ'')
    (hτ''le : τ'' ≤ edgeTau' τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) {M : ℕ} (σ : Fin M → ℝ) (k : ℕ),
      DensityAssumptions τ N σ → RegularEdge τ N σ k →
        OneXmOn c N σ (edgeDomain τ₂ τ'' N σ k) := by
  by_cases hτ1 : τ ≤ 1
  swap
  · exact ⟨1, one_pos, fun N M σ k h _ => absurd (edgeLow_facts h).2.1 hτ1⟩
  have hτ0 : 0 < τ := lt_of_lt_of_le hτ₂ hτ₂τ
  obtain ⟨-, -, -, -, -, -, -, hρτ, ht, -, -⟩ := edgeLow_consts hτ0 hτ1
  have hCm : 0 < mBoundConst τ₂ := by unfold mBoundConst genPropConst; positivity
  set c := min (τ / 2) (edgeTau' τ / mBoundConst τ₂) with hcdef
  have hc : 0 < c := lt_min (half_pos hτ0) (div_pos ht hCm)
  refine ⟨oneXmConst c (mBoundConst τ₂), lt_min (by norm_num) (by positivity),
    fun N M σ k h hk z hz i => ?_⟩
  have h₂ : DensityAssumptions τ₂ N σ := h.mono hτ₂ hτ₂τ
  obtain ⟨-, hmC, hmlow⟩ := gen_prop_m_specDomain h₂ hz.1
  have hη : 0 < z.im := hz.1.1
  refine one_add_mul_ge_of_mz_reg h.nonneg hc hCm hmC (fun s hs => ?_) i
  by_cases hηs : z.im < edgeTau' τ
  · -- `η < τ'`: (z-a_taylor) and (reg: edge)
    have hE : |z.re - edgeVal N σ k| ≤ τ'' := by
      obtain ⟨-, h1, h2⟩ := hz
      rw [abs_le]; constructor <;> linarith
    have hza : ‖z - edgeVal N σ k‖ ≤ edgeTau0 τ := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (z - edgeVal N σ k)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero, abs_of_pos hη] at h1
      have : edgeTau0 τ = 4 * edgeTau' τ := by unfold edgeTau'; ring
      rw [this]; linarith
    obtain ⟨hloc, -⟩ := z_a_taylor h hk hη.le hza
    have hm : mExt N σ z = mFun N σ z := by simp [mExt, hη]
    rw [hm] at hloc
    have hreg := edgeLow_reg h hk s hs
    have htri : ‖((xCrit N σ k + s⁻¹ : ℝ) : ℂ)‖ ≤
        ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ + ‖mFun N σ z - xCrit N σ k‖ := by
      have e : ((xCrit N σ k + s⁻¹ : ℝ) : ℂ) =
          (mFun N σ z + ((s⁻¹ : ℝ) : ℂ)) - (mFun N σ z - xCrit N σ k) := by
        push_cast; ring
      rw [e]
      exact norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at htri
    have : c ≤ τ / 2 := min_le_left _ _
    linarith
  · -- `η ≥ τ'`: `Im m ≥ C_m(τ₂)⁻¹ η` (Lemma 4.10 at `τ₂`)
    have hηl : edgeTau' τ ≤ z.im := not_lt.mp hηs
    have h1 : (mFun N σ z).im ≤ ‖mFun N σ z + ((s⁻¹ : ℝ) : ℂ)‖ := by
      have := Complex.im_le_norm (mFun N σ z + ((s⁻¹ : ℝ) : ℂ))
      simpa using this
    have h2 : c ≤ edgeTau' τ / mBoundConst τ₂ := min_le_right _ _
    have h3 : edgeTau' τ / mBoundConst τ₂ ≤ (mBoundConst τ₂)⁻¹ * z.im := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hηl (inv_nonneg.2 hCm.le)
    linarith

/-- Theorem 3.14 (i) with the window `τ''` fixed by the edge regularity at `τ` and the domain
parameter `τ₂ ≤ τ` (lower cutoff `N^{−1+τ₂}`). -/
theorem edge_law' (τ τ₂ τ'' : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ₂ : 0 < τ₂) (hτ₂τ : τ₂ ≤ τ)
    (hτ'' : 0 < τ'') (hτ''le : τ'' ≤ edgeTau' τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      AnisotropicLawAt N ε D Sig X (edgeDomain τ₂ τ'' N (specOf Sig) k) ∧
        AveragedLawAt N ε D Sig X (edgeDomain τ₂ τ'' N (specOf Sig) k) := by
  obtain ⟨c, hc, hx⟩ := oneXm_edge' τ τ₂ τ'' hτ₂ hτ₂τ hτ'' hτ''le
  obtain ⟨C₀, C₁, K₀, N₅, h₅⟩ := stab_edge2_weak' τ τ₂ τ'' hτ₂ hτ₂τ hτ'' hτ''le
  obtain ⟨ε₁, D₁, hε₁, N₁, h₁⟩ := gen_iso_aniso τ₂ c C ε D hτ₂ hc hε
  obtain ⟨ε₂, D₂, hε₂, N₂, h₂⟩ := gen_iso_avg τ₂ c C ε D hτ₂ hc hε
  obtain ⟨N₃, h₃⟩ := gauss_avg_input τ₂ c C₀ C₁ K₀ ε₁ D₁ hτ₂ hc hε₁
  obtain ⟨N₄, h₄⟩ := gauss_avg_input τ₂ c C₀ C₁ K₀ ε₂ D₂ hτ₂ hc hε₂
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1), fun N hN Ω _ _ M Sig X k hm hk => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hB : max N₅ 1 ≤ N := le_of_max_le_right hN
  have hN1 : 1 ≤ N := le_of_max_le_right hB
  have hτ : 0 < τ := lt_of_lt_of_le hτ₂ hτ₂τ
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hm2 : IsModel τ₂ C M N Sig X := hm.mono hτ₂ hτ₂τ
  have hS := spectralDomain_edgeDomain τ₂ τ'' N (specOf Sig) k
  have hxk := hx N (specOf Sig) k hda hk
  have hst := h₅ N (le_of_max_le_left hB) (specOf Sig) k hda hk
  have hgm : IsModel τ₂ gaussMoment M N Sig (gaussX M N) :=
    isModel_gaussX hN1 hm2.ratio_ge hm2.ratio_le hm2.sigma
  have g₁ := h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig _ hgm hS hxk hst
  have g₂ := h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig _ hgm hS hxk hst
  exact ⟨h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X _ hm2 hS hxk g₁.1,
    h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X _ hm2 hS hxk g₂.1
      (averagedPhiLawAt_inv_iff.1 g₂.2)⟩

/-- The domain `{z ∈ 𝐃(τ₂, N) : E ∈ edgeWin τ}`. -/
def lowDomain (τ τ₂ : ℝ) (N : ℕ) (σ : Fin M → ℝ) : Set ℂ :=
  {z | z ∈ specDomain τ₂ N ∧ z.re ∈ edgeWin τ N σ}

/-- The averaged law of Theorem 3.6 at the domain parameter `τ₂ ≤ τ`, for `E ∈ edgeWin τ`, under
the hypotheses of Theorem 3.6 at `τ` (every edge with `a_k ≥ τ/2` regular at `τ/2`). -/
theorem LL_G_low (τ τ₂ : ℝ) (C : ℕ → ℝ) (c : ℝ → ℝ) (ε D : ℝ) (hτ₂ : 0 < τ₂) (hτ₂τ : τ₂ ≤ τ)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → τ / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (τ / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) → RegularBulk c N (specOf Sig) k) →
      AveragedLawAt N ε D Sig X (lowDomain τ τ₂ N (specOf Sig)) := by
  have h2 : 0 < τ₂ / 2 := half_pos hτ₂
  have hc' : 0 < coverTau τ₂ := coverTau_pos hτ₂
  have hce : coverTau τ₂ ≤ edgeTau' (τ₂ / 2) := min_le_left _ _
  have hc4 : coverTau τ₂ ≤ τ₂ / 4 := min_le_right _ _
  obtain ⟨N₁, h₁⟩ := edge_law (τ₂ / 2) (coverTau τ₂) C ε D h2 hc' hce hε
  obtain ⟨N₂, h₂⟩ := bulk_law (τ₂ / 2) (coverTau τ₂) c C ε D h2 hc' hε
  obtain ⟨N₃, h₃⟩ := outside_law (τ₂ / 2) (coverTau τ₂) C ε D h2 hc' hε
  obtain ⟨N₄, h₄⟩ := high_law τ₂ C ε D hτ₂ hε
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) 1, fun N hN Ω _ _ M Sig X hm hedge hbulk => ?_⟩
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hmτ₂ : IsModel τ₂ C M N Sig X := hm.mono hτ₂ hτ₂τ
  have hm2 : IsModel (τ₂ / 2) C M N Sig X := hm.mono h2 (by linarith)
  have hda : DensityAssumptions τ₂ N (specOf Sig) :=
    hmτ₂.diagModel_specOf.densityAssumptions hτ₂
  intro z hz
  rcases specDomain_cover hτ₂ hN1 hda hz.1 with hh | ho | ⟨k, hk1, hk2, hb⟩ |
    ⟨l, hl1, hl2, -, he⟩
  · exact (h₄ N (le_of_max_le_right (le_of_max_le_right hA)) M Sig X hmτ₂).2 z hh
  · exact (h₃ N (le_of_max_le_left (le_of_max_le_right hA)) M Sig X hm2).2 z ho
  · exact (h₂ N (le_of_max_le_right (le_of_max_le_left hA)) M Sig X k hm2
      (hbulk k hk1 hk2)).2 z hb
  · have hal : τ / 2 ≤ edgeVal N (specOf Sig) l := by
      rcases hz.2 with h3 | ⟨l', hl1', hl2', hal', hd'⟩
      · have h1 := he.2.2
        have h3' : 3 * τ / 4 ≤ z.re := h3
        linarith
      · by_cases hll : l = l'
        · subst hll
          exact hal'
        · exfalso
          have hsep := (hedge l' hl1' hl2' hal').2.2.2.1 l hl1 hl2 hll
          have hE := he.2
          have h4 : |edgeVal N (specOf Sig) l' - edgeVal N (specOf Sig) l| ≤
              τ / 8 + coverTau τ₂ := by
            rw [abs_le] at hd' ⊢
            constructor <;> linarith [hE.1, hE.2, hd'.1, hd'.2]
          linarith
    have hreg := regularEdge_mono (hedge l hl1 hl2 hal) (by linarith : τ₂ / 2 ≤ τ / 2)
    exact (h₁ N (le_of_max_le_left (le_of_max_le_left hA)) M Sig X l hm2 hreg).2 z he

/-! ## Instances

The parameter hypotheses at `τ = 1/5`, `τ₂ = 1/10` (resp. `1/20`), `τ'' = τ'(1/5)`. The
hypotheses on the spectral data inside the statements are discharged where the imported results
allow it (`DensityAssumptions (1/5)` for `σ ≡ 1` on `Fin 3`, `N = 6`); the edge regularity is kept
as a binder (conditional instance). -/

example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel (1 / 5) gaussMoment M N Sig X →
      (∀ k, 1 ≤ k → k ≤ 2 * numBands N (specOf Sig) → 1 / 5 / 2 ≤ edgeVal N (specOf Sig) k →
        RegularEdge (1 / 5 / 2) N (specOf Sig) k) →
      (∀ k, 1 ≤ k → k ≤ numBands N (specOf Sig) →
        RegularBulk (fun t => min t 1 / 50) N (specOf Sig) k) →
      AveragedLawAt N 1 1 Sig X (lowDomain (1 / 5) (1 / 20) N (specOf Sig)) :=
  LL_G_low (1 / 5) (1 / 20) gaussMoment (fun t => min t 1 / 50) 1 1 (by norm_num) (by norm_num)
    one_pos

#print axioms stab_edge2_weak'
#print axioms oneXm_edge'
#print axioms edge_law'
#print axioms lowDomain
#print axioms LL_G_low

end Anisotropic
