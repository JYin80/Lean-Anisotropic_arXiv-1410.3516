module

public import Anisotropic.Gaussian.Parity
public import Anisotropic.Gaussian.BadEvent
public import Anisotropic.Framework.DominationMoment
public import Anisotropic.Density.Stability.Domains

@[expose] public section

/-!
# Lemma 6.2 and Proposition 6.1 for Gaussian `X`

Section 6. Contents:
* the core estimate of Lemma 6.2 for `Σ = diag(σ)` and Gaussian `Y`: the entrywise law at level
  `(ε/4, D₁)` gives the anisotropic law (Definition 3.20 (ii)) at level `(ε, D)`. The bilinear
  form `⟨v, B w⟩` of `B = Σ̲⁻¹(G − Π)Σ̲⁻¹` splits into its diagonal part, bounded by `Λ`, and the
  off-diagonal part `𝒵`, whose moment `E|𝒵|^p` is bounded through the parity argument; Markov's
  inequality with the moment `p` finishes;
* Proposition 6.1 (i) and (ii) at fixed `N`: writing `Σ = U D Uᵀ`, the rotation
  `(O_M, O_N) = (Uᵀ, 1)` of (rotation of matrix) and the rotation invariance of the Gaussian law
  transport the anisotropic and averaged laws from `D = diag(specOf Σ)` to `Σ`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Lemma 6.2: the core estimate and its transport -/

/-- The moment order `p = 2 max(1, ⌈2(D+1)/ε⌉)`. -/
def lawPow (ε D : ℝ) : ℕ := 2 * max 1 ⌈2 * (D + 1) / ε⌉₊

/-- The hypothesis exponent `D₁ = max(8p + 4, D + 4)`. -/
def lawD1 (ε D : ℝ) : ℝ := max (8 * (lawPow ε D : ℝ) + 4) (D + 4)

/-- `K_m(p) = 2 (2p − 1)!!`. -/
def lawMomConst (p : ℕ) : ℝ := 2 * ((2 * p - 1).doubleFactorial : ℝ)

/-! ## Test vectors -/

/-- `|v| = 1` gives `Σ_s v_s² = 1`. -/
private theorem lemma62_sum_sq {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : testNorm v = 1) :
    ∑ s, v s ^ 2 = 1 := by
  have h0 : 0 ≤ ∑ s, v s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg (v s)
  have h := Real.sq_sqrt h0
  unfold testNorm at hv
  rw [hv] at h
  linarith

/-- `Σ_s |v_s| |w_s| ≤ 1` for unit `v`, `w`. -/
private theorem lemma62_sum_abs_mul_le {ι : Type*} [Fintype ι] {v w : ι → ℝ}
    (hv : testNorm v = 1) (hw : testNorm w = 1) : ∑ s, |v s| * |w s| ≤ 1 := by
  have h : ∀ s, |v s| * |w s| ≤ (v s ^ 2 + w s ^ 2) / 2 := by
    intro s
    nlinarith [sq_nonneg (|v s| - |w s|), sq_abs (v s), sq_abs (w s)]
  calc ∑ s, |v s| * |w s| ≤ ∑ s, (v s ^ 2 + w s ^ 2) / 2 := Finset.sum_le_sum fun s _ => h s
    _ = ((∑ s, v s ^ 2) + ∑ s, w s ^ 2) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = 1 := by rw [lemma62_sum_sq hv, lemma62_sum_sq hw]; norm_num

/-- `|v| = 0` forces `v = 0`. -/
private theorem lemma62_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : testNorm v = 0) :
    v = 0 := by
  unfold testNorm at hv
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun s _ => sq_nonneg (v s)),
    Finset.sum_eq_zero_iff_of_nonneg fun s _ => sq_nonneg (v s)] at hv
  funext s
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hv s (Finset.mem_univ s))

/-- `|c v| = |c| |v|`. -/
private theorem lemma62_testNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    testNorm (c • v) = |c| * testNorm v := by
  unfold testNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- `⟨a v, A (b w)⟩ = a b ⟨v, A w⟩`. -/
private theorem lemma62_testBilin_smul {ι : Type*} [Fintype ι] (a b : ℝ) (v : ι → ℝ)
    (A : Matrix ι ι ℂ) (w : ι → ℝ) :
    testBilin (a • v) A (b • w) = ((a * b : ℝ) : ℂ) * testBilin v A w := by
  simp only [testBilin, dotProduct, mulVec, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `b ↦ |⟨v, F(b) w⟩|` is measurable when every entry of `F` is. -/
private theorem lemma62_measurable_testBilin {ι β : Type*} [Fintype ι] [MeasurableSpace β]
    (v w : ι → ℝ) {F : β → Matrix ι ι ℂ} (hF : ∀ s t, Measurable fun b => F b s t) :
    Measurable fun b => ‖testBilin v (F b) w‖ := by
  refine Measurable.norm ?_
  simp only [testBilin, dotProduct, mulVec]
  refine Finset.measurable_sum _ fun s _ => measurable_const.mul ?_
  exact Finset.measurable_sum _ fun t _ => (hF s t).mul measurable_const

/-! ## Exponents -/

/-- `p = lawPow ε D` is even. -/
private theorem lemma62_even (ε D : ℝ) : Even (lawPow ε D) := even_two_mul _

/-- `p = lawPow ε D ≥ 1`. -/
private theorem lemma62_one_le (ε D : ℝ) : 1 ≤ lawPow ε D := by
  unfold lawPow
  have := le_max_left 1 ⌈2 * (D + 1) / ε⌉₊
  omega

/-- The Markov exponent: `D + 1 ≤ (3ε/4 − ε/2) p`. -/
private theorem lemma62_exp {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    D + 1 ≤ (3 * ε / 4 - ε / 2) * (lawPow ε D : ℝ) := by
  set m : ℕ := max 1 ⌈2 * (D + 1) / ε⌉₊ with hm
  have hp : (lawPow ε D : ℝ) = 2 * (m : ℝ) := by simp [lawPow, hm]
  have h1 : 2 * (D + 1) / ε ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have h2 : 2 * (D + 1) ≤ (m : ℝ) * ε := (div_le_iff₀ hε).1 h1
  rw [hp]
  nlinarith

/-- `x^{-(D + k)} = x^{-D} / x^k`. -/
private theorem lemma62_rpow_neg_add {x : ℝ} (hx : 0 < x) (D : ℝ) (k : ℕ) :
    x ^ (-(D + k)) = x ^ (-D) / x ^ k := by
  rw [neg_add, Real.rpow_add hx, Real.rpow_neg hx.le (k : ℝ), Real.rpow_natCast, div_eq_mul_inv]

/-- `x^{a k} = (x^a)^k`. -/
private theorem lemma62_rpow_mul_nat {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (k : ℕ) :
    x ^ (a * k) = (x ^ a) ^ k := by
  rw [Real.rpow_mul hx, Real.rpow_natCast]

/-- The thresholds for `N₀`: `N ≥ 2`, `N^{ε/4} ≥ max(2, K_m)`, `τ^p N^{p+1} ≥ K_b (1 + τ⁻¹)` and
`N² ≥ 2 (1 + τ⁻¹)²`. -/
private theorem lemma62_thresholds {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N ∧ max 2 (lawMomConst (lawPow ε D)) ≤ (N : ℝ) ^ (ε / 4) ∧
      lawBadConst τ (lawPow ε D) * (1 + τ⁻¹) ≤ τ ^ lawPow ε D * (N : ℝ) ^ (lawPow ε D + 1) ∧
      2 * (1 + τ⁻¹) ^ 2 ≤ (N : ℝ) ^ 2 := by
  have h1 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have h2 : ∀ᶠ N : ℕ in atTop, max 2 (lawMomConst (lawPow ε D)) ≤ (N : ℝ) ^ (ε / 4) :=
    ((tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have h3 : ∀ᶠ N : ℕ in atTop,
      lawBadConst τ (lawPow ε D) * (1 + τ⁻¹) ≤ τ ^ lawPow ε D * (N : ℝ) ^ (lawPow ε D + 1) :=
    (Tendsto.const_mul_atTop (pow_pos hτ _) ((tendsto_pow_atTop (Nat.succ_ne_zero _)).comp
      tendsto_natCast_atTop_atTop)).eventually_ge_atTop _
  have h4 : ∀ᶠ N : ℕ in atTop, 2 * (1 + τ⁻¹) ^ 2 ≤ (N : ℝ) ^ 2 :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  exact eventually_atTop.1 (h1.and (h2.and (h3.and h4)))

/-! ## The core estimate for unit test vectors -/

section Core

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Lemma 6.2 for `Σ = diag(σ)`, Gaussian `Y` and unit `v`, `w`, at one `N` above the
thresholds: `ℙ(|⟨v, B w⟩| > N^ε Ψ) ≤ N^{-D}`. -/
private theorem lemma62_unit {τ ε D : ℝ} (hτ : 0 < τ) (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N)
    (hX : max 2 (lawMomConst (lawPow ε D)) ≤ (N : ℝ) ^ (ε / 4))
    (hB : lawBadConst τ (lawPow ε D) * (1 + τ⁻¹) ≤
      τ ^ lawPow ε D * (N : ℝ) ^ (lawPow ε D + 1))
    (hK : 2 * (1 + τ⁻¹) ^ 2 ≤ (N : ℝ) ^ 2)
    {σ : Fin M → ℝ} {Y : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ}
    (hY : IsGaussianEnsemble Y) (hσ : ∀ i, 0 < σ i) (hM : (M : ℝ) / N ≤ τ⁻¹)
    (hS : S ⊆ specDomain τ N) (h : EntrywiseLawAt N (ε / 4) (lawD1 ε D) (diagonal σ) Y S)
    {z : ℂ} (hz : z ∈ S) {v w : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (hw : testNorm w = 1) :
    ℙ {ω | (N : ℝ) ^ ε * Psi N σ z < ‖testBilin v (lawMat (diagonal σ) (Y ω) z) w‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  set p := lawPow ε D with hp_def
  set Ψ := Psi N σ z with hΨ_def
  set X : ℝ := (N : ℝ) ^ (ε / 4) with hX_def
  set Kb := lawBadConst τ p with hKb_def
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hzD := hS hz
  have hzim : 0 < z.im := hzD.1
  have hzle : z.im ≤ τ⁻¹ := hzD.2.2.2.2
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hκ : 0 < 1 + τ⁻¹ := by linarith
  have hM' : (M : ℝ) ≤ τ⁻¹ * N := (div_le_iff₀ hNpos).1 hM
  have hMN : (M : ℝ) + N ≤ (1 + τ⁻¹) * N := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- `Ψ ≥ 1/(Nη) ≥ τ/N > 0`
  have hΨ1 : 1 / (N * z.im) ≤ Ψ := by
    rw [hΨ_def, Psi]
    linarith [Real.sqrt_nonneg ((mFun N σ z).im / (N * z.im))]
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hNpos hzim
  have hΨpos : 0 < Ψ := lt_of_lt_of_le (div_pos one_pos hNη) hΨ1
  have hΨτ : τ / N ≤ Ψ := by
    refine le_trans ?_ hΨ1
    rw [div_le_div_iff₀ hNpos hNη]
    have : τ * z.im ≤ 1 := by
      calc τ * z.im ≤ τ * τ⁻¹ := mul_le_mul_of_nonneg_left hzle hτ.le
        _ = 1 := mul_inv_cancel₀ hτ.ne'
    nlinarith
  -- `X = N^{ε/4}`
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXK : lawMomConst p ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hp1 : 1 ≤ p := lemma62_one_le ε D
  have hXp : X ≤ X ^ p := le_self_pow₀ hX1 (by omega)
  have hXε2 : (N : ℝ) ^ (ε / 2) = X * X := by
    rw [hX_def, ← Real.rpow_add hNpos]; congr 1; ring
  have hXε34 : (N : ℝ) ^ (3 * ε / 4) = X ^ 3 := by
    rw [hX_def, ← lemma62_rpow_mul_nat hNpos.le]; congr 1; push_cast; ring
  have hXε : (N : ℝ) ^ ε = X ^ 4 := by
    rw [hX_def, ← lemma62_rpow_mul_nat hNpos.le]; congr 1; push_cast; ring
  -- the bad event `{Λ > N^{ε/4} Ψ}` and `a = (M + N)² N^{-D₁}`
  set a : ℝ := ((M : ℝ) + N) ^ 2 * (N : ℝ) ^ (-lawD1 ε D) with ha_def
  have hbad : ℙ {ω | X * Ψ < Lambda σ (Y ω) z} ≤ ENNReal.ofReal a :=
    measure_Lambda_gt_le hσ h hz hzim
  obtain ⟨hint, hIle⟩ :=
    integral_LambdaO_pow_le hτ hN1 hY hσ hM' hzD p (mul_nonneg (by linarith) hΨpos.le) hbad
  obtain ⟨hint2, hmom⟩ := moment_offPart_le hY hσ hzim hv hw (lemma62_even ε D) hint
  -- `√a ≤ (1 + τ⁻¹) / N^{4p+1}`
  have hD₁p : -lawD1 ε D ≤ -((8 * p + 4 : ℕ) : ℝ) := by
    rw [neg_le_neg_iff, lawD1]; push_cast; exact le_max_left _ _
  have hNpow : ∀ k : ℕ, 0 < (N : ℝ) ^ k := fun k => pow_pos hNpos k
  have ha1 : a ≤ ((1 + τ⁻¹) / (N : ℝ) ^ (4 * p + 1)) ^ 2 := by
    have e1 : (N : ℝ) ^ (-lawD1 ε D) ≤ ((N : ℝ) ^ (8 * p + 4))⁻¹ := by
      refine (Real.rpow_le_rpow_of_exponent_le hN1' hD₁p).trans (le_of_eq ?_)
      rw [Real.rpow_neg hNpos.le, Real.rpow_natCast]
    have e2 : ((M : ℝ) + N) ^ 2 ≤ ((1 + τ⁻¹) * N) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMN 2
    calc a ≤ ((1 + τ⁻¹) * N) ^ 2 * ((N : ℝ) ^ (8 * p + 4))⁻¹ :=
          mul_le_mul e2 e1 (Real.rpow_nonneg hNpos.le _) (by positivity)
      _ = ((1 + τ⁻¹) / (N : ℝ) ^ (4 * p + 1)) ^ 2 := by
          have : (N : ℝ) ^ (8 * p + 4) = (N : ℝ) ^ 2 * ((N : ℝ) ^ (4 * p + 1)) ^ 2 := by
            rw [← pow_mul, ← pow_add]; congr 1; ring
          rw [this, div_pow]
          field_simp
  have hsa : √a ≤ (1 + τ⁻¹) / (N : ℝ) ^ (4 * p + 1) := by
    calc √a ≤ √(((1 + τ⁻¹) / (N : ℝ) ^ (4 * p + 1)) ^ 2) := Real.sqrt_le_sqrt ha1
      _ = _ := Real.sqrt_sq (div_nonneg hκ.le (hNpow _).le)
  -- the bad term is `≤ Ψ^p`
  have hKb0 : 0 ≤ Kb := by
    rw [hKb_def, lawBadConst]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ.le _)) (Real.sqrt_nonneg _)
  have hbadterm : Kb * (N : ℝ) ^ (2 * p) * √a ≤ Ψ ^ p := by
    calc Kb * (N : ℝ) ^ (2 * p) * √a
        ≤ Kb * (N : ℝ) ^ (2 * p) * ((1 + τ⁻¹) / (N : ℝ) ^ (4 * p + 1)) :=
          mul_le_mul_of_nonneg_left hsa (mul_nonneg hKb0 (hNpow _).le)
      _ = Kb * (1 + τ⁻¹) / (N : ℝ) ^ (2 * p + 1) := by
          have : (N : ℝ) ^ (4 * p + 1) = (N : ℝ) ^ (2 * p) * (N : ℝ) ^ (2 * p + 1) := by
            rw [← pow_add]; congr 1; ring
          rw [this]
          field_simp
      _ ≤ τ ^ p / (N : ℝ) ^ p := by
          rw [div_le_div_iff₀ (hNpow _) (hNpow _)]
          have : (N : ℝ) ^ (2 * p + 1) = (N : ℝ) ^ (p + 1) * (N : ℝ) ^ p := by
            rw [← pow_add]; congr 1; ring
          rw [this, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hB (hNpow _).le
      _ = (τ / N) ^ p := (div_pow _ _ _).symm
      _ ≤ Ψ ^ p := pow_le_pow_left₀ (div_nonneg hτ.le hNpos.le) hΨτ p
  -- the moment bound `E|𝒵|^p ≤ (N^{ε/2} Ψ)^p`
  have hdf : (0 : ℝ) ≤ ((2 * p - 1).doubleFactorial : ℝ) := Nat.cast_nonneg _
  have hΨXp : Ψ ^ p ≤ (X * Ψ) ^ p :=
    pow_le_pow_left₀ hΨpos.le (le_mul_of_one_le_left hΨpos.le hX1) p
  have hmom' : ∫ ω, ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖ ^ p ≤
      ((N : ℝ) ^ (ε / 2) * Ψ) ^ p := by
    calc ∫ ω, ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖ ^ p
        ≤ ((2 * p - 1).doubleFactorial : ℝ) * ∫ ω, LambdaO σ (Y ω) z ^ p := hmom
      _ ≤ ((2 * p - 1).doubleFactorial : ℝ) * ((X * Ψ) ^ p + (X * Ψ) ^ p) := by
          refine mul_le_mul_of_nonneg_left (hIle.trans ?_) hdf
          linarith
      _ = lawMomConst p * X ^ p * Ψ ^ p := by rw [lawMomConst, mul_pow]; ring
      _ ≤ X ^ p * X ^ p * Ψ ^ p := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hXK.trans hXp)
            (pow_nonneg (by linarith) _)) (pow_nonneg hΨpos.le _)
      _ = ((N : ℝ) ^ (ε / 2) * Ψ) ^ p := by rw [hXε2, mul_pow, mul_pow]
  -- Markov at `(ε/2 → 3ε/4, D + 1)`
  have hdom : ℙ {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ <
      ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
    DomAt.of_moment (ε := ε / 2) (ξ := fun ω => ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖)
      p hN1 (lemma62_exp hε D) (fun ω => norm_nonneg _) hΨpos hint2 hmom'
  -- assembly
  have hsub : {ω | (N : ℝ) ^ ε * Ψ < ‖testBilin v (lawMat (diagonal σ) (Y ω) z) w‖} ⊆
      {ω | X * Ψ < Lambda σ (Y ω) z} ∪
        {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ < ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc hω
    obtain ⟨h1, h2⟩ := hc
    set B := lawMat (diagonal σ) (Y ω) z with hB_def
    have hΛ0 : 0 ≤ Lambda σ (Y ω) z :=
      (norm_nonneg _).trans (norm_lawMat_le_Lambda hσ (Y ω) hzim (Sum.inr ⟨0, by omega⟩)
        (Sum.inr ⟨0, by omega⟩)).1
    have hdiag : ‖∑ s, (v s : ℂ) * B s s * w s‖ ≤ Lambda σ (Y ω) z := by
      calc ‖∑ s, (v s : ℂ) * B s s * w s‖ ≤ ∑ s, ‖(v s : ℂ) * B s s * w s‖ := norm_sum_le _ _
        _ ≤ ∑ s, Lambda σ (Y ω) z * (|v s| * |w s|) := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
            have hle := (norm_lawMat_le_Lambda hσ (Y ω) hzim s s).1
            calc |v s| * ‖B s s‖ * |w s| = ‖B s s‖ * (|v s| * |w s|) := by ring
              _ ≤ Lambda σ (Y ω) z * (|v s| * |w s|) :=
                mul_le_mul_of_nonneg_right hle (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = Lambda σ (Y ω) z * ∑ s, |v s| * |w s| := by rw [Finset.mul_sum]
        _ ≤ Lambda σ (Y ω) z * 1 :=
            mul_le_mul_of_nonneg_left (lemma62_sum_abs_mul_le hv hw) hΛ0
        _ = Lambda σ (Y ω) z := mul_one _
    have htot : ‖testBilin v B w‖ ≤ (N : ℝ) ^ ε * Ψ := by
      rw [testBilin_eq_diag_add_offPart]
      calc ‖∑ s, (v s : ℂ) * B s s * w s + offPart v B w‖
          ≤ ‖∑ s, (v s : ℂ) * B s s * w s‖ + ‖offPart v B w‖ := norm_add_le _ _
        _ ≤ X * Ψ + X ^ 3 * Ψ := by rw [← hXε34]; linarith
        _ ≤ X ^ 4 * Ψ := by
            rw [← add_mul]
            refine mul_le_mul_of_nonneg_right ?_ hΨpos.le
            have h3 : X ≤ X ^ 3 := le_self_pow₀ hX1 (by norm_num)
            have h4 : X ^ 3 * 2 ≤ X ^ 4 := by
              rw [show X ^ 4 = X ^ 3 * X by ring]
              exact mul_le_mul_of_nonneg_left hX2 (by positivity)
            linarith
        _ = (N : ℝ) ^ ε * Ψ := by rw [hXε]
    linarith
  -- `a + N^{-(D+1)} ≤ N^{-D}`
  have hND : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNpos _
  have ha2 : a ≤ (N : ℝ) ^ (-D) / 2 := by
    have e1 : (N : ℝ) ^ (-lawD1 ε D) ≤ (N : ℝ) ^ (-D) / (N : ℝ) ^ 4 := by
      rw [← lemma62_rpow_neg_add hNpos]
      refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
      rw [neg_le_neg_iff, lawD1]; push_cast; exact le_max_right _ _
    have e2 : ((M : ℝ) + N) ^ 2 ≤ ((1 + τ⁻¹) * N) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMN 2
    calc a ≤ ((1 + τ⁻¹) * N) ^ 2 * ((N : ℝ) ^ (-D) / (N : ℝ) ^ 4) :=
          mul_le_mul e2 e1 (Real.rpow_nonneg hNpos.le _) (by positivity)
      _ = (N : ℝ) ^ (-D) * ((1 + τ⁻¹) ^ 2 / (N : ℝ) ^ 2) := by
          field_simp
      _ ≤ (N : ℝ) ^ (-D) * (1 / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hND.le
          rw [div_le_iff₀ (hNpow 2)]
          linarith
      _ = (N : ℝ) ^ (-D) / 2 := by ring
  have hb2 : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 2 := by
    have := lemma62_rpow_neg_add hNpos D 1
    rw [Nat.cast_one, pow_one] at this
    rw [this]
    exact div_le_div_of_nonneg_left hND.le (by norm_num) hN2'
  have ha0 : 0 ≤ a := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hNpos.le _)
  calc ℙ {ω | (N : ℝ) ^ ε * Ψ < ‖testBilin v (lawMat (diagonal σ) (Y ω) z) w‖}
      ≤ ℙ ({ω | X * Ψ < Lambda σ (Y ω) z} ∪
        {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ < ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖}) :=
        measure_mono hsub
    _ ≤ ℙ {ω | X * Ψ < Lambda σ (Y ω) z} +
        ℙ {ω | (N : ℝ) ^ (3 * ε / 4) * Ψ < ‖offPart v (lawMat (diagonal σ) (Y ω) z) w‖} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := add_le_add hbad hdom
    _ = ENNReal.ofReal (a + (N : ℝ) ^ (-(D + 1))) :=
        (ENNReal.ofReal_add ha0 (Real.rpow_nonneg hNpos.le _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (by linarith)

end Core

/-- The core estimate: for Gaussian `Y` and `Σ = diag(σ)`, the entrywise law at
`(ε/4, D₁)` gives the anisotropic law at `(ε, D)`. -/
theorem anisoLaw_diag_gauss (τ ε D : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (Y : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsGaussianEnsemble Y → (∀ i, 0 < σ i) → τ ≤ (M : ℝ) / N → (M : ℝ) / N ≤ τ⁻¹ →
      S ⊆ specDomain τ N → EntrywiseLawAt N (ε / 4) (lawD1 ε D) (diagonal σ) Y S →
      AnisotropicLawAt N ε D (diagonal σ) Y S := by
  obtain ⟨N₀, hN₀⟩ := lemma62_thresholds hτ hε D
  refine ⟨N₀, fun N hN => ?_⟩
  intro Ω _ _ M σ Y S hY hσ _ hMτ hS h z hz v w
  obtain ⟨hN2, hX, hB, hK⟩ := hN₀ N hN
  have hPsi : Psi N (specOf (diagonal σ)) z = Psi N σ z := by
    unfold Psi
    rw [mFun_specOf_diagonal]
  change ℙ {ω | (N : ℝ) ^ ε * (Psi N (specOf (diagonal σ)) z * testNorm v * testNorm w) <
    ‖testBilin v (lawMat (diagonal σ) (Y ω) z) w‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))
  rw [hPsi]
  by_cases hv0 : testNorm v = 0
  · have : v = 0 := lemma62_eq_zero hv0
    subst this
    refine le_trans (measure_mono (t := ∅) fun ω hω => ?_) (by simp)
    simp [hv0, testBilin, dotProduct, mulVec] at hω
  by_cases hw0 : testNorm w = 0
  · have : w = 0 := lemma62_eq_zero hw0
    subst this
    refine le_trans (measure_mono (t := ∅) fun ω hω => ?_) (by simp)
    simp [hw0, testBilin, dotProduct, mulVec] at hω
  have hva : 0 < testNorm v := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv0)
  have hwb : 0 < testNorm w := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hw0)
  set a := testNorm v with ha
  set b := testNorm w with hb
  have hv1 : testNorm (a⁻¹ • v) = 1 := by
    rw [lemma62_testNorm_smul, ← ha, abs_of_pos (inv_pos.2 hva), inv_mul_cancel₀ hva.ne']
  have hw1 : testNorm (b⁻¹ • w) = 1 := by
    rw [lemma62_testNorm_smul, ← hb, abs_of_pos (inv_pos.2 hwb), inv_mul_cancel₀ hwb.ne']
  have hv' : v = a • (a⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hva.ne', one_smul]
  have hw' : w = b • (b⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hwb.ne', one_smul]
  have hab : 0 < a * b := mul_pos hva hwb
  refine le_trans (measure_mono fun ω hω => ?_)
    (lemma62_unit hτ hε hN2 hX hB hK hY hσ hMτ hS h hz hv1 hw1)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have e : ‖testBilin v (lawMat (diagonal σ) (Y ω) z) w‖ =
      ‖testBilin (a⁻¹ • v) (lawMat (diagonal σ) (Y ω) z) (b⁻¹ • w)‖ * (a * b) := by
    conv_lhs => rw [hv', hw']
    rw [lemma62_testBilin_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hab, mul_comm]
  rw [e, show (N : ℝ) ^ ε * (Psi N σ z * a * b) = (N : ℝ) ^ ε * Psi N σ z * (a * b) by ring] at hω
  exact lt_of_mul_lt_mul_right hω hab.le

section Transport

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- `Uᵀ` is orthogonal with `U`. -/
private theorem lemma62_transpose_mem {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin K) ℝ) : Uᵀ ∈ Matrix.orthogonalGroup (Fin K) ℝ :=
  (Matrix.mem_orthogonalGroup_iff _ _).2 (by
    rw [transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hU)

/-- (rotation of matrix) with `(O_M, O_N) = (Uᵀ, 1)` and `Uᵀ Σ U = D`, solved for `Σ`:
`B(Σ, A) = Qᵀ B(D, Uᵀ A) Q` with `Q = diag(Uᵀ, 1)`. -/
private theorem lemma62_lawMat_eq {N : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    {U : Matrix (Fin M) (Fin M) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin M) ℝ)
    (hUD : Uᵀ * Sig * U = diagonal (specOf Sig)) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) :
    lawMat Sig A z = (cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)))ᵀ *
      lawMat (diagonal (specOf Sig)) (Uᵀ * A * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ) z *
        cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)) := by
  have hUT := lemma62_transpose_mem hU
  have hON : (1 : Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.orthogonalGroup (Fin N) ℝ := one_mem _
  have hP := blockQ_mem hUT hON
  have hPP : (cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)))ᵀ *
      cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)) = 1 := by
    rw [← cplx_transpose, ← cplx_mul, (Matrix.mem_orthogonalGroup_iff' _ _).1 hP, cplx_one]
  have e := lawMat_rotate hUT hON Sig A z
  rw [transpose_transpose, hUD] at e
  rw [← e]
  change _ = (cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)))ᵀ *
    (cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)) * lawMat Sig A z *
      (cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ)))ᵀ) *
        cplx (blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ))
  calc lawMat Sig A z = 1 * lawMat Sig A z * 1 := by simp
    _ = _ := by rw [← hPP]; simp only [Matrix.mul_assoc]

/-- Proposition 6.1 (i), transport step at fixed `N`: the anisotropic law for `(X, D(Σ))`
gives the anisotropic law for `(X, Σ)`, Gaussian `X`. -/
theorem aniso_of_diag {N : ℕ} {ε D : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.IsHermitian)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : IsGaussianEnsemble X) {S : Set ℂ}
    (h : AnisotropicLawAt N ε D (diagonal (specOf Sig)) X S) :
    AnisotropicLawAt N ε D Sig X S := by
  obtain ⟨U, hU, hUD⟩ := exists_orth_diag hSig
  have hUT := lemma62_transpose_mem hU
  have hON : (1 : Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.orthogonalGroup (Fin N) ℝ := one_mem _
  have hP := blockQ_mem hUT hON
  intro z hz v w
  set P := blockQ Uᵀ (1 : Matrix (Fin N) (Fin N) ℝ) with hP_def
  have h1 := h z hz (P *ᵥ v) (P *ᵥ w)
  rw [specOf_diagonal_specOf, testNorm_orth hP, testNorm_orth hP] at h1
  have hξ : Measurable fun A : Matrix (Fin M) (Fin N) ℝ =>
      ‖testBilin (P *ᵥ v) (lawMat (diagonal (specOf Sig)) A z) (P *ᵥ w)‖ :=
    lemma62_measurable_testBilin _ _ fun s t => measurable_lawMat_apply _ z s t
  have h2 := hX.domAt_rotate hUT hON
    (ξ := fun A => ‖testBilin (P *ᵥ v) (lawMat (diagonal (specOf Sig)) A z) (P *ᵥ w)‖)
    (ζ := fun _ => Psi N (specOf Sig) z * testNorm v * testNorm w) hξ measurable_const h1
  have hf : (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖) = fun ω =>
      ‖testBilin (P *ᵥ v) (lawMat (diagonal (specOf Sig)) (Uᵀ * X ω * (1 : Matrix (Fin N)
        (Fin N) ℝ)ᵀ) z) (P *ᵥ w)‖ := by
    funext ω
    rw [lemma62_lawMat_eq hU hUD, testBilin_conj]
  change DomAt N ε D (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖)
    (fun _ => Psi N (specOf Sig) z * testNorm v * testNorm w)
  rw [hf]
  exact h2

/-- Proposition 6.1 (ii) at fixed `N`: the averaged law for `(X, D(Σ))` gives the averaged
law for `(X, Σ)`, Gaussian `X`. -/
theorem gauss_averaged {N : ℕ} {ε D : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.IsHermitian) {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : IsGaussianEnsemble X)
    {S : Set ℂ} (h : AveragedLawAt N ε D (diagonal (specOf Sig)) X S) :
    AveragedLawAt N ε D Sig X S := by
  obtain ⟨U, hU, hUD⟩ := exists_orth_diag hSig
  have hUT := lemma62_transpose_mem hU
  have hON : (1 : Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.orthogonalGroup (Fin N) ℝ := one_mem _
  intro z hz
  have h1 := h z hz
  unfold ODomAt at h1 ⊢
  rw [specOf_diagonal_specOf] at h1
  have hξ : Measurable fun A : Matrix (Fin M) (Fin N) ℝ =>
      ‖mN (diagonal (specOf Sig)) A z - mFun N (specOf Sig) z‖ :=
    ((measurable_mN _ z).sub_const _).norm
  have h2 := hX.domAt_rotate hUT hON
    (ξ := fun A => ‖mN (diagonal (specOf Sig)) A z - mFun N (specOf Sig) z‖)
    (ζ := fun _ => 1 / (N * z.im)) hξ measurable_const h1
  have e : ∀ A : Matrix (Fin M) (Fin N) ℝ,
      mN (diagonal (specOf Sig)) (Uᵀ * A * (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ) z = mN Sig A z := by
    intro A
    have := mN_rotate hUT hON Sig A z
    rwa [transpose_transpose, hUD] at this
  simp only [e] at h2
  exact h2

end Transport

/-! ## Checks -/

section Checks

/-- The values at `ε = D = 1`: `p = 8`, `D₁ = 68` and `K_m = 2 · 15!! = 4054050`. -/
example : lawPow 1 1 = 8 ∧ lawD1 1 1 = 68 ∧ lawMomConst (lawPow 1 1) = 4054050 := by
  have h : lawPow 1 1 = 8 := by
    have : ⌈(2 * (1 + 1) / 1 : ℝ)⌉₊ = 4 := by norm_num
    unfold lawPow
    rw [this]
    rfl
  refine ⟨h, ?_, ?_⟩
  · simp only [lawD1, h]
    norm_num
  · rw [h]
    simp [lawMomConst, Nat.doubleFactorial]
    norm_num

end Checks

end Anisotropic

#print axioms Anisotropic.anisoLaw_diag_gauss
#print axioms Anisotropic.aniso_of_diag
#print axioms Anisotropic.gauss_averaged
