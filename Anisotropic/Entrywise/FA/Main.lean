module

public import Anisotropic.Entrywise.FA.Moment
public import Anisotropic.Framework.DominationMoment

@[expose] public section

/-! # Lemma 5.6 (fluctuation averaging) for `Σ = diag(σ)`

The high-moment reduction for deterministic weights, the Taylor expansion of the random weights
`σ_i²/(1 + m_N σ_i)²` of (avg_conclusion2) at `m`, and the two conclusions (avg_conclusion) and
(avg_conclusion2) of Lemma 5.6, pointwise in `z`, with explicit exponents. -/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Lemma 5.6: deterministic weights, the Taylor expansion of the random weights, and
(avg_conclusion), (avg_conclusion2) -/

/-- `p(ε, D) = ⌈D/ε⌉ + 1`. -/
def faP (ε D : ℝ) : ℕ := ⌈D / ε⌉₊ + 1

/-- `ε₁(ε, c₀) = min(ε, c₀)/64`; it is also the LDE level `ε_L`. -/
def faEps (ε c₀ : ℝ) : ℝ := min ε c₀ / 64

/-- `D₁(ε, D) = 8 p(ε, D) + 2`. -/
def faD (ε D : ℝ) : ℝ := 8 * (faP ε D : ℝ) + 2

/-- `X ≤ N^a` once `N ≥ |X|^{1/a}`. -/
private theorem main_le_rpow {a X : ℝ} (ha : 0 < a) {N : ℕ} (hN : ⌈|X| ^ (1 / a)⌉₊ ≤ N) :
    X ≤ (N : ℝ) ^ a := by
  have h1 : |X| ^ (1 / a) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc X ≤ |X| := le_abs_self X
    _ = (|X| ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul (abs_nonneg X), one_div_mul_cancel ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

/-- The high-moment reduction: Lemma 5.6 for deterministic weights `|a| ≤ A`, with the
explicit `ε₁ = faEps ε c₀`, `D₁ = faD ε D`. -/
theorem fluct_avg_det (τ c c₀ : ℝ) (C : ℕ → ℝ) (ε D A : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hc₀ : 0 < c₀) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-c₀) →
      DomAt N (faEps ε c₀) (faD ε D) (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-c₀)) →
      DomAt N (faEps ε c₀) (faD ε D) (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
      (∀ a : Fin N → ℂ, (∀ μ, ‖a μ‖ ≤ A) →
        DomAt N ε D (fun ω => ‖ZavgN σ (X ω) z a‖) (fun _ => Υ ^ 2)) ∧
      (∀ a : Fin M → ℂ, (∀ i, ‖a i‖ ≤ A) →
        DomAt N ε D (fun ω => ‖ZavgM σ (X ω) z a‖) (fun _ => Υ ^ 2)) := by
  set p := faP ε D with hp
  set e₁ := faEps ε c₀ with he₁
  have hmin : 0 < min ε c₀ := lt_min hε hc₀
  have he₁0 : 0 < e₁ := by rw [he₁, faEps]; positivity
  have he₁c : e₁ ≤ c₀ / 2 := by
    rw [he₁, faEps]; have := min_le_right ε c₀; linarith
  have he₁ε : e₁ ≤ ε / 64 := by
    rw [he₁, faEps]; have := min_le_left ε c₀; linarith
  obtain ⟨N₁, hN₁⟩ := fa_moment τ c c₀ C p e₁ e₁ (faD ε D) A hτ hc hc₀ he₁0.le he₁c he₁0 he₁c
    (by rw [faD])
  have hp1 : (1 : ℝ) ≤ p := by
    rw [hp, faP]; push_cast; linarith [(Nat.cast_nonneg ⌈D / ε⌉₊ : (0 : ℝ) ≤ _)]
  have hpε : D + ε ≤ ε * p := by
    have h1 : D / ε ≤ ⌈D / ε⌉₊ := Nat.le_ceil _
    have h2 : D ≤ ε * ⌈D / ε⌉₊ := by rwa [div_le_iff₀ hε, mul_comm] at h1
    rw [hp, faP]; push_cast; linarith
  have hpεpos : 0 < (p : ℝ) * ε / 8 := by positivity
  set Cp := faMomConst p τ c A with hCp
  refine ⟨max N₁ (max 1 ⌈|Cp| ^ (1 / ((p : ℝ) * ε / 8))⌉₊),
    fun N hN Ω _ _ M σ X hX z hz hx Υ hΥN hΥc₀ hΛ hΛo => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hNC : Cp ≤ (N : ℝ) ^ ((p : ℝ) * ε / 8) :=
    main_le_rpow hpεpos (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hΥ : 0 < Υ := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hΥN
  obtain ⟨hNa, hMa⟩ :=
    hN₁ N (le_trans (le_max_left _ _) hN) M σ X hX z hz hx Υ hΥN hΥc₀ hΛ hΛo
  have key : ∀ x : ℝ, x ≤ Cp * (N : ℝ) ^ (4 * (p : ℝ) * (e₁ + e₁)) * Υ ^ (4 * p) →
      x ≤ ((N : ℝ) ^ (ε / 8) * Υ ^ 2) ^ (2 * p) := by
    intro x hx'
    refine hx'.trans ?_
    have h1 : (N : ℝ) ^ (4 * (p : ℝ) * (e₁ + e₁)) ≤ (N : ℝ) ^ ((p : ℝ) * ε / 8) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by nlinarith)
    have h2 : ((N : ℝ) ^ (ε / 8) * Υ ^ 2) ^ (2 * p) =
        (N : ℝ) ^ ((p : ℝ) * ε / 8) * (N : ℝ) ^ ((p : ℝ) * ε / 8) * Υ ^ (4 * p) := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← pow_mul,
        ← Real.rpow_add hNpos]
      congr 2
      · push_cast; ring
      · ring
    rw [h2]
    gcongr
  have hD : D ≤ (ε - ε / 8) * ((2 * p : ℕ) : ℝ) := by
    have e : (ε - ε / 8) * ((2 * p : ℕ) : ℝ) = (7 / 4) * (ε * p) := by push_cast; ring
    have : 0 ≤ ε * p := by positivity
    rw [e]; linarith
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨hint, hmom⟩ := hNa a ha
    exact DomAt.of_moment (2 * p) hN1 hD (fun _ => norm_nonneg _) (pow_pos hΥ 2) hint
      (key _ hmom)
  · obtain ⟨hint, hmom⟩ := hMa a ha
    exact DomAt.of_moment (2 * p) hN1 hD (fun _ => norm_nonneg _) (pow_pos hΥ 2) hint
      (key _ hmom)

/-- `a^{(k)}_i = (k+1) σ_i² (−σ_i)^k / (1 + m σ_i)^{k+2}`, the Taylor coefficients of
`σ_i²/(1 + w σ_i)²` at `w = m`. -/
def taylorW (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) (k : ℕ) (i : Fin M) : ℂ :=
  ((k + 1 : ℕ) : ℂ) * (σ i : ℂ) ^ 2 * (-(σ i : ℂ)) ^ k / (1 + σ i * mFun N σ z) ^ (k + 2)

/-- `|a^{(k)}_i| ≤ (k+1)(τ⁻¹c⁻¹)^{k+2}`. -/
theorem norm_taylorW_le {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (hσ0 : ∀ i, 0 ≤ σ i) (hσ : ∀ i, σ i ≤ τ⁻¹) {z : ℂ}
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (k : ℕ) (i : Fin M) :
    ‖taylorW N σ z k i‖ ≤ (k + 1) * (τ⁻¹ * c⁻¹) ^ (k + 2) := by
  have hb := hx i
  set b := ‖1 + (σ i : ℂ) * mFun N σ z‖ with hbdef
  have hbpos : 0 < b := lt_of_lt_of_le hc hb
  have hs : ‖(σ i : ℂ)‖ = σ i := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ0 i)]
  have hnorm : ‖taylorW N σ z k i‖ = (k + 1) * σ i ^ (k + 2) / b ^ (k + 2) := by
    simp only [taylorW, norm_div, norm_mul, norm_pow, norm_neg, hs, Complex.norm_natCast]
    rw [← hbdef]
    push_cast
    ring
  rw [hnorm, div_le_iff₀ (pow_pos hbpos _)]
  have hk : (0 : ℝ) ≤ k + 1 := by positivity
  have h1 : σ i ^ (k + 2) ≤ τ⁻¹ ^ (k + 2) := pow_le_pow_left₀ (hσ0 i) (hσ i) _
  have h2 : τ⁻¹ ≤ τ⁻¹ * c⁻¹ * b := by
    have : 1 ≤ c⁻¹ * b := by rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith
    have hτ0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
    calc τ⁻¹ = τ⁻¹ * 1 := (mul_one _).symm
      _ ≤ τ⁻¹ * (c⁻¹ * b) := mul_le_mul_of_nonneg_left this hτ0
      _ = τ⁻¹ * c⁻¹ * b := by ring
  have h3 : τ⁻¹ ^ (k + 2) ≤ (τ⁻¹ * c⁻¹) ^ (k + 2) * b ^ (k + 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (inv_pos.2 hτ).le h2 _
  calc (k + 1) * σ i ^ (k + 2) ≤ (k + 1) * ((τ⁻¹ * c⁻¹) ^ (k + 2) * b ^ (k + 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) hk
    _ = (k + 1) * (τ⁻¹ * c⁻¹) ^ (k + 2) * b ^ (k + 2) := by ring

/-- `Σ_{k<K} (k+1) x^k · (1 − x)² = 1 − (K+1) x^K + K x^{K+1}`. -/
private theorem main_sum_mul_sq (x : ℂ) (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℂ) * x ^ k) * (1 - x) ^ 2 =
      1 - ((K + 1 : ℕ) : ℂ) * x ^ K + (K : ℂ) * x ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/-- The weight expansion: if `τ⁻¹c⁻¹|w − m| ≤ 1/4`, then
`|σ_i²/(1 + w σ_i)² − Σ_{k<K} a^{(k)}_i (w − m)^k| ≤ 2(K+1) τ⁻²c⁻² (τ⁻¹c⁻¹|w − m|)^K`. -/
theorem weight_taylor {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (hσ0 : ∀ i, 0 ≤ σ i) (hσ : ∀ i, σ i ≤ τ⁻¹) {z : ℂ}
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (w : ℂ)
    (hw : τ⁻¹ * c⁻¹ * ‖w - mFun N σ z‖ ≤ 1 / 4) (K : ℕ) (i : Fin M) :
    ‖(σ i : ℂ) ^ 2 / (1 + w * σ i) ^ 2 -
        ∑ k ∈ Finset.range K, taylorW N σ z k i * (w - mFun N σ z) ^ k‖ ≤
      2 * (K + 1) * (τ⁻¹ * c⁻¹) ^ 2 * (τ⁻¹ * c⁻¹ * ‖w - mFun N σ z‖) ^ K := by
  set m := mFun N σ z with hm
  set s : ℂ := (σ i : ℂ) with hsdef
  set b : ℂ := 1 + s * m with hbdef
  set d := w - m with hd
  set t := τ⁻¹ * c⁻¹ with ht
  have hb : c ≤ ‖b‖ := hx i
  have hbpos : 0 < ‖b‖ := lt_of_lt_of_le hc hb
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbpos
  have hs : ‖s‖ = σ i := by
    rw [hsdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ0 i)]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hsb : ‖s‖ / ‖b‖ ≤ t := by
    rw [div_le_iff₀ hbpos, hs, ht]
    have h1 : 1 ≤ c⁻¹ * ‖b‖ := by rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith
    have hτ0 : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
    calc σ i ≤ τ⁻¹ := hσ i
      _ = τ⁻¹ * 1 := (mul_one _).symm
      _ ≤ τ⁻¹ * (c⁻¹ * ‖b‖) := mul_le_mul_of_nonneg_left h1 hτ0
      _ = τ⁻¹ * c⁻¹ * ‖b‖ := by ring
  set x : ℂ := -(s * d) / b with hxdef
  have hxle : ‖x‖ ≤ t * ‖d‖ := by
    rw [hxdef, norm_div, norm_neg, norm_mul, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hsb (norm_nonneg _)
  have hx4 : ‖x‖ ≤ 1 / 4 := hxle.trans hw
  have h1x : 3 / 4 ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one] at this; linarith
  have h1x0 : (1 : ℂ) - x ≠ 0 := by
    intro h; rw [h, norm_zero] at h1x; linarith
  have hbx : b * x = -(s * d) := by rw [hxdef]; field_simp
  have hw' : 1 + w * s = b * (1 - x) := by linear_combination hbx - hbdef + s * hd
  have hterm : ∀ k : ℕ,
      taylorW N σ z k i * d ^ k = s ^ 2 / b ^ 2 * (((k + 1 : ℕ) : ℂ) * x ^ k) := by
    intro k
    simp only [taylorW]
    rw [← hsdef, ← hm, ← hbdef, hxdef, div_pow, ← neg_mul, mul_pow, pow_add]
    field_simp
  have hsum : ∑ k ∈ Finset.range K, taylorW N σ z k i * d ^ k =
      s ^ 2 / b ^ 2 * ∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℂ) * x ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hterm k
  have hS : ∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℂ) * x ^ k =
      (1 - ((K + 1 : ℕ) : ℂ) * x ^ K + (K : ℂ) * x ^ (K + 1)) / (1 - x) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 h1x0)]; exact main_sum_mul_sq x K
  have hdiff : s ^ 2 / (1 + w * s) ^ 2 - ∑ k ∈ Finset.range K, taylorW N σ z k i * d ^ k =
      s ^ 2 / b ^ 2 * (x ^ K * (((K + 1 : ℕ) : ℂ) * (1 - x) + x) / (1 - x) ^ 2) := by
    rw [hsum, hw', hS]
    field_simp
    push_cast
    ring
  rw [hdiff]
  set u := ‖1 - x‖ with hu
  have hupos : 0 < u := by linarith
  have hY : ‖((K + 1 : ℕ) : ℂ) * (1 - x) + x‖ ≤ (K + 1) * u + 1 / 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, ← hu]
    push_cast
    linarith
  have hQ : ((K + 1) * u + 1 / 4) / u ^ 2 ≤ 2 * (K + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith [mul_nonneg hK0 (sub_nonneg.2 h1x)]
  have hnorm : ‖s ^ 2 / b ^ 2 * (x ^ K * (((K + 1 : ℕ) : ℂ) * (1 - x) + x) / (1 - x) ^ 2)‖ =
      (‖s‖ / ‖b‖) ^ 2 * (‖x‖ ^ K * (‖((K + 1 : ℕ) : ℂ) * (1 - x) + x‖ / u ^ 2)) := by
    rw [hu]; simp only [norm_mul, norm_div, norm_pow]; ring
  rw [hnorm]
  have hA : (‖s‖ / ‖b‖) ^ 2 ≤ t ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) hsb 2
  have hB : ‖x‖ ^ K ≤ (t * ‖d‖) ^ K := pow_le_pow_left₀ (norm_nonneg _) hxle K
  have hC : ‖((K + 1 : ℕ) : ℂ) * (1 - x) + x‖ / u ^ 2 ≤ 2 * (K + 1) :=
    (div_le_div_of_nonneg_right hY (by positivity)).trans hQ
  calc (‖s‖ / ‖b‖) ^ 2 * (‖x‖ ^ K * (‖((K + 1 : ℕ) : ℂ) * (1 - x) + x‖ / u ^ 2))
      ≤ t ^ 2 * ((t * ‖d‖) ^ K * (2 * (K + 1))) := by
        gcongr
    _ = 2 * (K + 1) * t ^ 2 * (t * ‖d‖) ^ K := by ring

/-- `K(c₀) = ⌈2/c₀⌉`, the number of Taylor terms. -/
def taylorK (c₀ : ℝ) : ℕ := ⌈2 / c₀⌉₊

/-- `A = K (τ⁻¹c⁻¹ + 1)^{K+1}`, a bound for `|a^{(k)}_i|`, `k < K`. -/
def taylorA (τ c : ℝ) (K : ℕ) : ℝ := K * (τ⁻¹ * c⁻¹ + 1) ^ (K + 1)

/-- The level `D₁` of the random-weight bound: `max(D₁(ε/2, D+2), D+2)`. -/
def faD2 (ε D : ℝ) : ℝ := max (faD (ε / 2) (D + 2)) (D + 2)

/-- `2(K+1) ≤ 4^K` for `K ≥ 1`. -/
private theorem main_two_mul_le_four_pow {K : ℕ} (hK : 1 ≤ K) : 2 * (K + 1) ≤ 4 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K _ ih => rw [pow_succ]; omega

/-- On `Λ ≤ N^{−c₀/2}` with `N^{c₀/4} ≥ 4C_Θ(τ⁻¹c⁻¹ + 1)`: `τ⁻¹c⁻¹|m_N − m| ≤ N^{−c₀/4}/4`
and `|m_N − m| ≤ 1` ((Theta_leq_Lambda)). -/
private theorem main_dev_le {τ c c₀ : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hc₀ : 0 < c₀) {N : ℕ}
    {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i)
    (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (hN1 : 1 ≤ N)
    (hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (-(c₀ / 2)))
    (hT : 4 * ThetaConst τ * (τ⁻¹ * c⁻¹ + 1) ≤ (N : ℝ) ^ (c₀ / 4)) :
    τ⁻¹ * c⁻¹ * ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ (N : ℝ) ^ (-(c₀ / 4)) / 4 ∧
      ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ 1 := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have ht0 : 0 ≤ τ⁻¹ * c⁻¹ := by positivity
  have hCΘ : 0 < ThetaConst τ := by unfold ThetaConst; positivity
  have hθ : ‖mN (diagonal σ) Xm z - mFun N σ z‖ ≤ ThetaConst τ * Lambda σ Xm z := by
    have h1 := Theta_le_Lambda h hσ Xm z (by omega)
    have h0 : 0 ≤ ThetaM σ Xm z := norm_nonneg _
    unfold Theta ThetaN at h1
    linarith
  have hq0 : 0 < (N : ℝ) ^ (-(c₀ / 4)) := Real.rpow_pos_of_pos hNpos _
  have hq1 : (N : ℝ) ^ (-(c₀ / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hqq : (N : ℝ) ^ (-(c₀ / 2)) = (N : ℝ) ^ (-(c₀ / 4)) * (N : ℝ) ^ (-(c₀ / 4)) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have he : (N : ℝ) ^ (c₀ / 4) * (N : ℝ) ^ (-(c₀ / 4)) = 1 := by
    rw [← Real.rpow_add hNpos]; simp
  generalize (N : ℝ) ^ (-(c₀ / 4)) = q at hq0 hq1 hqq he
  generalize ‖mN (diagonal σ) Xm z - mFun N σ z‖ = d at hθ ⊢
  generalize τ⁻¹ * c⁻¹ = t at ht0 hT ⊢
  rw [hqq] at hΛ
  have hTq : 4 * ThetaConst τ * (t + 1) * q ≤ 1 := by
    calc 4 * ThetaConst τ * (t + 1) * q ≤ (N : ℝ) ^ (c₀ / 4) * q :=
          mul_le_mul_of_nonneg_right hT hq0.le
      _ = 1 := he
  have hdq : d ≤ ThetaConst τ * (q * q) := hθ.trans (mul_le_mul_of_nonneg_left hΛ hCΘ.le)
  have hA : 0 ≤ ThetaConst τ * q * q := by positivity
  have hB : 0 ≤ t * ThetaConst τ * q * q := by positivity
  constructor
  · nlinarith
  · nlinarith

/-- The Taylor remainder of the weights with `K = ⌈2/c₀⌉` terms: if
`τ⁻¹c⁻¹|w − m| ≤ N^{−c₀/4}/4`, then `|σ_i²/(1 + w σ_i)² − Σ_{k<K} a^{(k)}_i (w − m)^k| ≤
τ⁻²c⁻² N^{−1/2}`. -/
private theorem main_rho_le {τ c c₀ : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hc₀ : 0 < c₀) {N : ℕ}
    {σ : Fin M → ℝ} (hσ0 : ∀ i, 0 ≤ σ i) (hσ : ∀ i, σ i ≤ τ⁻¹) {z : ℂ}
    (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) (w : ℂ) (hN1 : 1 ≤ N)
    (hw : τ⁻¹ * c⁻¹ * ‖w - mFun N σ z‖ ≤ (N : ℝ) ^ (-(c₀ / 4)) / 4) (i : Fin M) :
    ‖(σ i : ℂ) ^ 2 / (1 + w * σ i) ^ 2 -
        ∑ k ∈ Finset.range (taylorK c₀), taylorW N σ z k i * (w - mFun N σ z) ^ k‖ ≤
      (τ⁻¹ * c⁻¹) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : 1 ≤ taylorK c₀ := by
    rw [taylorK, Nat.one_le_ceil_iff]; positivity
  have hKc : 2 ≤ (taylorK c₀ : ℝ) * c₀ := by
    have h1 : 2 / c₀ ≤ taylorK c₀ := Nat.le_ceil _
    rwa [div_le_iff₀ hc₀] at h1
  have hq0 : 0 < (N : ℝ) ^ (-(c₀ / 4)) := Real.rpow_pos_of_pos hNpos _
  have hq1 : (N : ℝ) ^ (-(c₀ / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hqK : ((N : ℝ) ^ (-(c₀ / 4))) ^ taylorK c₀ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have h1 := weight_taylor hτ hc hσ0 hσ hx w (hw.trans (by linarith)) (taylorK c₀) i
  refine h1.trans ?_
  have h4K : (2 * ((taylorK c₀ : ℝ) + 1)) ≤ 4 ^ taylorK c₀ := by
    exact_mod_cast main_two_mul_le_four_pow hK1
  have ht0 : 0 ≤ τ⁻¹ * c⁻¹ := by positivity
  have ha0 : 0 ≤ τ⁻¹ * c⁻¹ * ‖w - mFun N σ z‖ := by positivity
  generalize τ⁻¹ * c⁻¹ * ‖w - mFun N σ z‖ = a at hw ha0
  generalize (N : ℝ) ^ (-(c₀ / 4)) = q at hq0 hq1 hqK hw
  generalize τ⁻¹ * c⁻¹ = t at ht0
  generalize taylorK c₀ = K at h4K hqK
  have h2 : a ^ K ≤ (q / 4) ^ K := pow_le_pow_left₀ ha0 hw K
  have h4 : (0 : ℝ) < 4 ^ K := by positivity
  have h5 : 2 * (K + 1) * (q / 4) ^ K ≤ q ^ K := by
    rw [div_pow, mul_div_assoc', div_le_iff₀ h4]
    have : 0 ≤ q ^ K := by positivity
    nlinarith
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have hK0 : (0 : ℝ) ≤ 2 * (K + 1) := by positivity
  calc 2 * (K + 1) * t ^ 2 * a ^ K = t ^ 2 * (2 * (K + 1) * a ^ K) := by ring
    _ ≤ t ^ 2 * (2 * (K + 1) * (q / 4) ^ K) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK0) ht2
    _ ≤ t ^ 2 * q ^ K := mul_le_mul_of_nonneg_left h5 ht2
    _ ≤ t ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hqK ht2

/-- On the good event with `p = 1`: `|Z_i| ≤ K_L N^{2ε_F} Υ` (`Z_i = Z^{(∅)}_i`). -/
private theorem main_Zi_le {τ c c₀ εF Υ : ℝ} (hc : 0 < c) {N : ℕ} {σ : Fin M → ℝ}
    (h : DensityAssumptions τ N σ) (hσ : ∀ i, 0 < σ i) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hεF0 : 0 ≤ εF) (hεFc : εF ≤ c₀ / 2)
    (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ) (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (1 + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hgood : FaGood σ Xm z 1 c₀ εF εF Υ) (i : Fin M) :
    ‖Zi σ Xm z i‖ ≤ ldeZConst 1 τ c * ((N : ℝ) ^ εF * (N : ℝ) ^ εF * Υ) := by
  obtain ⟨hΛ, hΛo, -, hrow⟩ := hgood
  have h1 := hrow ∅ i (Finset.notMem_empty i) (by simp)
  rw [ZiS_empty] at h1
  have h2 := ldeZRow_le hc h hσ Xm hz hx hεF0 hεFc hΥN hΥc₀ hG hΛ hΛo ∅ (by simp) i
    (Finset.notMem_empty i)
  calc ‖Zi σ Xm z i‖ ≤ (N : ℝ) ^ εF * ldeZRow σ Xm z ∅ i := h1
    _ ≤ (N : ℝ) ^ εF * (ldeZConst 1 τ c * ((N : ℝ) ^ εF * Υ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ldeZConst 1 τ c * ((N : ℝ) ^ εF * (N : ℝ) ^ εF * Υ) := by ring

/-- `M⁻¹ Σ_i σ_i²(1 + m_N σ_i)⁻² Z_i = Σ_{k<K} (m_N − m)^k M⁻¹ Σ_i a^{(k)}_i Z_i
+ M⁻¹ Σ_i ρ_i Z_i`, with `ρ_i` the Taylor remainder of the weight at `w = m_N`. -/
private theorem main_split {N : ℕ} (σ : Fin M → ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (K : ℕ) :
    ZMavg σ Xm z = (∑ k ∈ Finset.range K, (mN (diagonal σ) Xm z - mFun N σ z) ^ k *
        ZavgM σ Xm z (taylorW N σ z k)) +
      (M : ℂ)⁻¹ * ∑ i, ((σ i : ℂ) ^ 2 / (1 + mN (diagonal σ) Xm z * σ i) ^ 2 -
        ∑ k ∈ Finset.range K, taylorW N σ z k i * (mN (diagonal σ) Xm z - mFun N σ z) ^ k) *
          Zi σ Xm z i := by
  have e1 : ∑ k ∈ Finset.range K, (mN (diagonal σ) Xm z - mFun N σ z) ^ k *
        ZavgM σ Xm z (taylorW N σ z k) =
      (M : ℂ)⁻¹ * ∑ i, (∑ k ∈ Finset.range K,
        taylorW N σ z k i * (mN (diagonal σ) Xm z - mFun N σ z) ^ k) * Zi σ Xm z i := by
    simp only [ZavgM, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e1, ← mul_add, ← Finset.sum_add_distrib, ZMavg]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|M⁻¹ Σ_i f_i g_i| ≤ B B'` when `|f_i| ≤ B`, `|g_i| ≤ B'` and `M ≥ 1`. -/
private theorem main_avg_le (hM : 0 < M) {f g : Fin M → ℂ} {B B' : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i, ‖f i‖ ≤ B) (hg : ∀ i, ‖g i‖ ≤ B') :
    ‖(M : ℂ)⁻¹ * ∑ i, f i * g i‖ ≤ B * B' := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hB' : ∀ i ∈ (Finset.univ : Finset (Fin M)), ‖f i * g i‖ ≤ B * B' := by
    intro i _
    rw [norm_mul]
    exact mul_le_mul (hf i) (hg i) (norm_nonneg _) hB
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hMpos]
  have h2 := (norm_sum_le _ _).trans (Finset.sum_le_sum hB')
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2

/-- The pointwise step of (avg_conclusion2): on the good event with `p = 1`, and when every
deterministic-weight average `M⁻¹ Σ_i a^{(k)}_i Z_i`, `k < K`, is at most `N^{ε/2}Υ²`,
`|M⁻¹ Σ_i σ_i² (1 + m_N σ_i)⁻² Z_i| ≤ N^ε Υ²`. -/
private theorem main_rand_pointwise {τ c c₀ ε εF Υ : ℝ} (hτ : 0 < τ) (hc : 0 < c)
    (hc₀ : 0 < c₀) {N : ℕ} {σ : Fin M → ℝ} (h : DensityAssumptions τ N σ)
    (hσ : ∀ i, 0 < σ i) (hM : 0 < M) (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ}
    (hz : z ∈ specDomain τ N) (hx : ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖)
    (hεF0 : 0 ≤ εF) (hεFc : εF ≤ c₀ / 64) (hεFε : εF ≤ ε / 4) (hN1 : 1 ≤ N)
    (hΥN : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ) (hΥc₀ : Υ ≤ (N : ℝ) ^ (-c₀))
    (hG : 4 ^ (1 + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹ ≤ (N : ℝ) ^ (c₀ / 2))
    (hT : 4 * ThetaConst τ * (τ⁻¹ * c⁻¹ + 1) ≤ (N : ℝ) ^ (c₀ / 4))
    (hK : (taylorK c₀ : ℝ) + (τ⁻¹ * c⁻¹) ^ 2 * ldeZConst 1 τ c ≤ (N : ℝ) ^ (ε / 2))
    (hgood : FaGood σ Xm z 1 c₀ εF εF Υ)
    (hk : ∀ k < taylorK c₀, ‖ZavgM σ Xm z (taylorW N σ z k)‖ ≤ (N : ℝ) ^ (ε / 2) * Υ ^ 2) :
    ‖ZMavg σ Xm z‖ ≤ (N : ℝ) ^ ε * Υ ^ 2 := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hΥ : 0 < Υ := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hΥN
  have hΛ : Lambda σ Xm z ≤ (N : ℝ) ^ (-(c₀ / 2)) :=
    hgood.1.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith))
  obtain ⟨hdw, hd1⟩ := main_dev_le hτ hc hc₀ h hσ Xm z hN1 hΛ hT
  have hρ := main_rho_le hτ hc hc₀ (fun i => (hσ i).le) h.bound_Sigma hx
    (mN (diagonal σ) Xm z) hN1 hdw
  have hZ := main_Zi_le hc h hσ Xm hz hx hεF0 (by linarith) hΥN hΥc₀ hG hgood
  have hKL0 : 0 ≤ ldeZConst 1 τ c := by
    have h1 : 0 < mAsympUpper c τ + 1 := by
      unfold mAsympUpper; linarith [le_max_left c⁻¹ (mBoundConst τ), inv_pos.2 hc]
    rw [ldeZConst]
    exact (mul_pos (mul_pos (by norm_num) h1) (pow_pos (inv_pos.2 hτ) 3)).le
  have hrem := main_avg_le hM (by positivity) hρ hZ
  have hmain : ‖∑ k ∈ Finset.range (taylorK c₀), (mN (diagonal σ) Xm z - mFun N σ z) ^ k *
      ZavgM σ Xm z (taylorW N σ z k)‖ ≤ taylorK c₀ * ((N : ℝ) ^ (ε / 2) * Υ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range (taylorK c₀), ‖(mN (diagonal σ) Xm z - mFun N σ z) ^ k *
        ZavgM σ Xm z (taylorW N σ z k)‖ ≤ (N : ℝ) ^ (ε / 2) * Υ ^ 2 := by
      intro k hk'
      rw [norm_mul, norm_pow]
      have h1 : ‖mN (diagonal σ) Xm z - mFun N σ z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hd1
      calc ‖mN (diagonal σ) Xm z - mFun N σ z‖ ^ k * ‖ZavgM σ Xm z (taylorW N σ z k)‖
          ≤ 1 * ((N : ℝ) ^ (ε / 2) * Υ ^ 2) :=
            mul_le_mul h1 (hk k (Finset.mem_range.1 hk')) (norm_nonneg _) zero_le_one
        _ = (N : ℝ) ^ (ε / 2) * Υ ^ 2 := one_mul _
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNN : (N : ℝ) ^ εF * (N : ℝ) ^ εF ≤ (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hNε : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  rw [main_split σ Xm z (taylorK c₀), hNε]
  refine (norm_add_le _ _).trans ((add_le_add hmain hrem).trans ?_)
  have hP : 0 < (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hE : 0 < (N : ℝ) ^ εF := Real.rpow_pos_of_pos hNpos _
  have hE2 : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hNpos _
  generalize (N : ℝ) ^ (-(1 / 2 : ℝ)) = P at hΥN hP
  generalize (N : ℝ) ^ εF = E at hNN hE
  generalize (N : ℝ) ^ (ε / 2) = E2 at hNN hK hE2
  generalize (τ⁻¹ * c⁻¹) = t at hK
  generalize ldeZConst 1 τ c = KL at hK hKL0
  generalize (taylorK c₀ : ℝ) = K at hK
  have hPΥ : P * Υ ≤ Υ ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hΥN hΥ.le
  have ht2 : 0 ≤ t ^ 2 * KL := by positivity
  have h1 : t ^ 2 * P * (KL * (E * E * Υ)) ≤ t ^ 2 * KL * (E2 * Υ ^ 2) := by
    have e : t ^ 2 * P * (KL * (E * E * Υ)) = t ^ 2 * KL * ((E * E) * (P * Υ)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hNN hPΥ (by positivity) hE2.le) ht2
  have h0 : 0 ≤ E2 * Υ ^ 2 := by positivity
  calc K * (E2 * Υ ^ 2) + t ^ 2 * P * (KL * (E * E * Υ))
      ≤ K * (E2 * Υ ^ 2) + t ^ 2 * KL * (E2 * Υ ^ 2) := by linarith
    _ = (K + t ^ 2 * KL) * (E2 * Υ ^ 2) := by ring
    _ ≤ E2 * (E2 * Υ ^ 2) := mul_le_mul_of_nonneg_right hK h0
    _ = E2 * E2 * Υ ^ 2 := by ring

/-- `N^{−(D₁−1)} + K N^{−(D+2)} ≤ N^{−D}` for `D₁ ≥ D + 2` and `N ≥ K + 1`. -/
private theorem main_prob_le {N K : ℕ} {D D₁ : ℝ} (hNK : K + 1 ≤ N) (hD : D + 2 ≤ D₁) :
    (N : ℝ) ^ (-(D₁ - 1)) + K * (N : ℝ) ^ (-(D + 2)) ≤ (N : ℝ) ^ (-D) := by
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hNK' : (K : ℝ) + 1 ≤ N := by exact_mod_cast hNK
  set y := (N : ℝ) ^ (-D) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hNpos _
  have h1 : (N : ℝ) ^ (-(D₁ - 1)) ≤ y * (N : ℝ)⁻¹ := by
    have e : (N : ℝ) ^ (-(D + 1)) = y * (N : ℝ)⁻¹ := by
      rw [hy, show -(D + 1) = -D + (-1) by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [← e]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have h2 : (N : ℝ) ^ (-(D + 2)) = y * ((N : ℝ) ^ 2)⁻¹ := by
    have e : (N : ℝ) ^ (-2 : ℝ) = ((N : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hNpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [show -(D + 2) = -D + (-2) by ring, Real.rpow_add hNpos, e]
  rw [h2]
  have h3 : (N : ℝ)⁻¹ + K * ((N : ℝ) ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_add_div _ _ hNpos.ne' (by positivity),
      div_le_one (by positivity)]
    have h4 : (N : ℝ) + K ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hNpos.le]
  calc (N : ℝ) ^ (-(D₁ - 1)) + K * (y * ((N : ℝ) ^ 2)⁻¹)
      ≤ y * (N : ℝ)⁻¹ + K * (y * ((N : ℝ) ^ 2)⁻¹) := by linarith
    _ = y * ((N : ℝ)⁻¹ + K * ((N : ℝ) ^ 2)⁻¹) := by ring
    _ ≤ y * 1 := mul_le_mul_of_nonneg_left h3 hy0.le
    _ = y := mul_one y

/-- (avg_conclusion2) with explicit `ε₁ = faEps (ε/2) c₀`, `D₁ = faD2 ε D`. -/
theorem fluct_avg_rand (τ c c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hc₀ : 0 < c₀) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-c₀) →
      DomAt N (faEps (ε / 2) c₀) (faD2 ε D) (fun ω => Lambda σ (X ω) z)
        (fun _ => (N : ℝ) ^ (-c₀)) →
      DomAt N (faEps (ε / 2) c₀) (faD2 ε D) (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
      DomAt N ε D (fun ω => ‖ZMavg σ (X ω) z‖) (fun _ => Υ ^ 2) := by
  set K := taylorK c₀ with hKdef
  set A := taylorA τ c K with hA
  set εF := faEps (ε / 2) c₀ with hεF
  set t := τ⁻¹ * c⁻¹ with ht
  have hmin : 0 < min (ε / 2) c₀ := lt_min (by linarith) hc₀
  have hεF0 : 0 < εF := by rw [hεF, faEps]; positivity
  have hεFc : εF ≤ c₀ / 64 := by
    rw [hεF, faEps]; have := min_le_right (ε / 2) c₀; linarith
  have hεFε : εF ≤ ε / 4 := by
    rw [hεF, faEps]; have := min_le_left (ε / 2) c₀; linarith
  have hD2 : faD (ε / 2) (D + 2) ≤ faD2 ε D := le_max_left _ _
  have hD2' : D + 2 ≤ faD2 ε D := le_max_right _ _
  obtain ⟨N₁, hN₁⟩ := fluct_avg_det τ c c₀ C (ε / 2) (D + 2) A hτ hc hc₀ (by linarith)
  obtain ⟨N₂, hN₂⟩ := faGood_highProb τ c₀ C 1 εF εF (faD2 ε D) hτ hεF0
  have hK1 : 1 ≤ K := by
    rw [hKdef, taylorK, Nat.one_le_ceil_iff]; positivity
  refine ⟨max (max N₁ N₂) (max (K + 1)
      (max ⌈|4 ^ (1 + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹| ^ (1 / (c₀ / 2))⌉₊
        (max ⌈|4 * ThetaConst τ * (t + 1)| ^ (1 / (c₀ / 4))⌉₊
          ⌈|(K : ℝ) + t ^ 2 * ldeZConst 1 τ c| ^ (1 / (ε / 2))⌉₊))), ?_⟩
  intro N hN Ω _ _ M σ X hX z hz hx Υ hΥN hΥc₀ hΛ hΛo
  have hN₁N : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂N : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hR : max (K + 1)
      (max ⌈|4 ^ (1 + 2) * τ⁻¹ ^ 2 * (mAsympLower τ)⁻¹| ^ (1 / (c₀ / 2))⌉₊
        (max ⌈|4 * ThetaConst τ * (t + 1)| ^ (1 / (c₀ / 4))⌉₊
          ⌈|(K : ℝ) + t ^ 2 * ldeZConst 1 τ c| ^ (1 / (ε / 2))⌉₊)) ≤ N :=
    le_trans (le_max_right _ _) hN
  simp only [max_le_iff] at hR
  obtain ⟨hNK, hNG, hNT, hNKL⟩ := hR
  have hG := main_le_rpow (by positivity : 0 < c₀ / 2) hNG
  have hT := main_le_rpow (by positivity : 0 < c₀ / 4) hNT
  have hKε := main_le_rpow (by positivity : 0 < ε / 2) hNKL
  have hN1 : 1 ≤ N := by omega
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hΥ : 0 < Υ := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hΥN
  have hda := hX.densityAssumptions hτ
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · have := hX.ratio_ge
      rw [h0, Nat.cast_zero, zero_div] at this
      linarith
    · exact h0
  -- the deterministic-weight averages at level `(ε/2, D+2)`
  have hΛd : DomAt N εF (faD (ε / 2) (D + 2)) (fun ω => Lambda σ (X ω) z)
      (fun _ => (N : ℝ) ^ (-c₀)) :=
    DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => (Real.rpow_pos_of_pos hNpos _).le)
      le_rfl hD2 hΛ
  have hΛod : DomAt N εF (faD (ε / 2) (D + 2)) (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) :=
    DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => hΥ.le) le_rfl hD2 hΛo
  have hdet := (hN₁ N hN₁N M σ X hX z hz hx Υ hΥN hΥc₀ hΛd hΛod).2
  have hwA : ∀ k < K, ∀ i, ‖taylorW N σ z k i‖ ≤ A := by
    intro k hk i
    refine (norm_taylorW_le hτ hc (fun i => (hX.pos i).le) hX.le hx k i).trans ?_
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have h1 : ((k : ℝ) + 1) ≤ K := by exact_mod_cast hk
    have h2 : (τ⁻¹ * c⁻¹) ^ (k + 2) ≤ (t + 1) ^ (K + 1) :=
      (pow_le_pow_left₀ ht0 (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    rw [hA, taylorA]
    exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)
  have hEk : ∀ k < K, DomAt N (ε / 2) (D + 2)
      (fun ω => ‖ZavgM σ (X ω) z (taylorW N σ z k)‖) (fun _ => Υ ^ 2) :=
    fun k hk => hdet _ (hwA k hk)
  -- the good event
  have hgood := hN₂ N hN₂N M σ X hX z Υ hΛ hΛo
  unfold HighProbAt at hgood
  unfold DomAt
  have hsub : {ω | (N : ℝ) ^ ε * Υ ^ 2 < ‖ZMavg σ (X ω) z‖} ⊆
      {ω | FaGood σ (X ω) z 1 c₀ εF εF Υ}ᶜ ∪
        ⋃ k ∈ Finset.range K,
          {ω | (N : ℝ) ^ (ε / 2) * Υ ^ 2 < ‖ZavgM σ (X ω) z (taylorW N σ z k)‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
      Finset.mem_range, not_or, not_not, not_exists, not_lt] at hcon
    obtain ⟨hg, hks⟩ := hcon
    have := main_rand_pointwise hτ hc hc₀ hda hX.pos hMpos (X ω) hz hx hεF0.le hεFc hεFε hN1
      hΥN hΥc₀ hG hT hKε hg (fun k hk => hks k hk)
    exact absurd hω (not_lt.mpr this)
  have hsum : ∑ k ∈ Finset.range K,
      ℙ {ω | (N : ℝ) ^ (ε / 2) * Υ ^ 2 < ‖ZavgM σ (X ω) z (taylorW N σ z k)‖} ≤
      ENNReal.ofReal (K * (N : ℝ) ^ (-(D + 2))) := by
    refine (Finset.sum_le_sum fun k hk => hEk k (Finset.mem_range.1 hk)).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hNpos _).le),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ℙ {ω | (N : ℝ) ^ ε * Υ ^ 2 < ‖ZMavg σ (X ω) z‖}
      ≤ ℙ ({ω | FaGood σ (X ω) z 1 c₀ εF εF Υ}ᶜ ∪
        ⋃ k ∈ Finset.range K,
          {ω | (N : ℝ) ^ (ε / 2) * Υ ^ 2 < ‖ZavgM σ (X ω) z (taylorW N σ z k)‖}) :=
        measure_mono hsub
    _ ≤ ℙ {ω | FaGood σ (X ω) z 1 c₀ εF εF Υ}ᶜ +
        ℙ (⋃ k ∈ Finset.range K,
          {ω | (N : ℝ) ^ (ε / 2) * Υ ^ 2 < ‖ZavgM σ (X ω) z (taylorW N σ z k)‖}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(faD2 ε D - 1))) +
        ENNReal.ofReal (K * (N : ℝ) ^ (-(D + 2))) :=
        add_le_add hgood ((measure_biUnion_finset_le _ _).trans hsum)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-(faD2 ε D - 1)) + K * (N : ℝ) ^ (-(D + 2))) :=
        (ENNReal.ofReal_add (Real.rpow_pos_of_pos hNpos _).le
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hNpos _).le)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
        ENNReal.ofReal_le_ofReal (main_prob_le hNK hD2')

/-- Lemma 5.6 (fluctuation averaging), pointwise in `z`; `Z_s = −(1 − E_s) G_ss⁻¹`. -/
theorem fluct_avg (τ c c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ > 0, ∃ D₁ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ), DiagModel τ C M N σ X →
      ∀ z ∈ specDomain τ N, (∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
      ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-c₀) →
      DomAt N ε₁ D₁ (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-c₀)) →
      DomAt N ε₁ D₁ (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
      DomAt N ε D (fun ω => ‖ZN σ (X ω) z‖) (fun _ => Υ ^ 2) ∧
        DomAt N ε D (fun ω => ‖ZMavg σ (X ω) z‖) (fun _ => Υ ^ 2) := by
  obtain ⟨N₁, hN₁⟩ := fluct_avg_det τ c c₀ C ε D 1 hτ hc hc₀ hε
  obtain ⟨N₂, hN₂⟩ := fluct_avg_rand τ c c₀ C ε D hτ hc hc₀ hε
  have hmin : 0 < min (ε / 2) c₀ := lt_min (by linarith) hc₀
  refine ⟨faEps (ε / 2) c₀, by rw [faEps]; positivity, max (faD ε D) (faD2 ε D),
    max (max N₁ N₂) 1, ?_⟩
  intro N hN Ω _ _ M σ X hX z hz hx Υ hΥN hΥc₀ hΛ hΛo
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hΥ0 : 0 ≤ Υ := le_trans (Real.rpow_pos_of_pos hNpos _).le hΥN
  have hc0 : ∀ _ : Ω, (0 : ℝ) ≤ (N : ℝ) ^ (-c₀) := fun _ => (Real.rpow_pos_of_pos hNpos _).le
  have hεle : faEps (ε / 2) c₀ ≤ faEps ε c₀ := by
    unfold faEps
    have : min (ε / 2) c₀ ≤ min ε c₀ := min_le_min (by linarith) le_rfl
    linarith
  have h1 := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) M σ X hX z hz
    hx Υ hΥN hΥc₀
    (DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) hc0 hεle (le_max_left _ _) hΛ)
    (DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => hΥ0) hεle (le_max_left _ _)
      hΛo)
  have h2 := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) M σ X hX z hz
    hx Υ hΥN hΥc₀
    (DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) hc0 le_rfl (le_max_right _ _) hΛ)
    (DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => hΥ0) le_rfl
      (le_max_right _ _) hΛo)
  refine ⟨?_, h2⟩
  have h3 := h1.1 (fun _ => 1) (fun _ => by simp)
  simpa only [ZavgN_one] using h3

/-! ## Checks -/

section Checks

example : faP 1 1 = 2 := by norm_num [faP]

example : taylorK (1 / 4) = 8 := by norm_num [taylorK]

example : faEps 1 (1 / 4) = 1 / 256 := by norm_num [faEps]

example : faD2 1 1 = 58 ∧ faEps (1 / 2) (1 / 4) = 1 / 256 := by
  norm_num [faD2, faD, faP, faEps]

/-- `fluct_avg_det` at `τ = 1/2`, `c = 1`, `c₀ = 1/4`, `C ≡ 2`, `ε = D = 1`, `A = 1`, where
`ε₁ = 1/256` and `D₁ = 18`. This is a conditional check: the models, `z`, `Υ`, the domination
hypotheses and the weights are binders, since the Rademacher model (`M = N = 2`, `σ ≡ 1`,
`z = 2i`) lies below the threshold `N₀`, which includes `N^{pε/8} ≥ C_p` and (G*)
`4^{p+2} τ⁻² c_as⁻¹ ≤ N^{c₀/2}`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, 1 ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) →
    DomAt N (1 / 256) 18 (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-(1 / 4 : ℝ))) →
    DomAt N (1 / 256) 18 (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
    (∀ a : Fin N → ℂ, (∀ μ, ‖a μ‖ ≤ 1) →
      DomAt N 1 1 (fun ω => ‖ZavgN σ (X ω) z a‖) (fun _ => Υ ^ 2)) ∧
    (∀ a : Fin M → ℂ, (∀ i, ‖a i‖ ≤ 1) →
      DomAt N 1 1 (fun ω => ‖ZavgM σ (X ω) z a‖) (fun _ => Υ ^ 2)) := by
  have h1 : faEps 1 (1 / 4) = 1 / 256 := by norm_num [faEps]
  have h2 : faD 1 1 = 18 := by norm_num [faD, faP]
  have h := fluct_avg_det (1 / 2) 1 (1 / 4) (fun _ => 2) 1 1 1 (by norm_num) one_pos
    (by norm_num) one_pos
  rwa [h1, h2] at h

/-- `fluct_avg_rand` at `τ = 1/2`, `c = 1`, `c₀ = 1/4`, `C ≡ 2`, `ε = D = 1`, where
`ε₁ = 1/256`, `D₁ = 58` and `K = 8`. This is a conditional check, as for `fluct_avg_det`: the
threshold `N₀` also includes `N ≥ K + 1`, `N^{c₀/4} ≥ 4 C_Θ (τ⁻¹c⁻¹ + 1)` and
`N^{ε/2} ≥ K + τ⁻²c⁻² K_L`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, 1 ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) →
    DomAt N (1 / 256) 58 (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-(1 / 4 : ℝ))) →
    DomAt N (1 / 256) 58 (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
    DomAt N 1 1 (fun ω => ‖ZMavg σ (X ω) z‖) (fun _ => Υ ^ 2) := by
  have h1 : faEps (1 / 2) (1 / 4) = 1 / 256 := by norm_num [faEps]
  have h2 : faD2 1 1 = 58 := by norm_num [faD2, faD, faP]
  have h := fluct_avg_rand (1 / 2) 1 (1 / 4) (fun _ => 2) 1 1 (by norm_num) one_pos
    (by norm_num) one_pos
  rwa [h1, h2] at h

/-- `fluct_avg` at `τ = 1/2`, `c = 1`, `c₀ = 1/4`, `C ≡ 2`, `ε = D = 1`. This is a conditional
check, as for `fluct_avg_det` and `fluct_avg_rand`: the models, `z`, `Υ` and the domination
hypotheses are binders. -/
example : ∃ ε₁ > 0, ∃ D₁ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (M : ℕ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
    DiagModel (1 / 2) (fun _ => 2) M N σ X →
    ∀ z ∈ specDomain (1 / 2) N, (∀ i, 1 ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖) →
    ∀ Υ : ℝ, (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Υ → Υ ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) →
    DomAt N ε₁ D₁ (fun ω => Lambda σ (X ω) z) (fun _ => (N : ℝ) ^ (-(1 / 4 : ℝ))) →
    DomAt N ε₁ D₁ (fun ω => LambdaO σ (X ω) z) (fun _ => Υ) →
    DomAt N 1 1 (fun ω => ‖ZN σ (X ω) z‖) (fun _ => Υ ^ 2) ∧
      DomAt N 1 1 (fun ω => ‖ZMavg σ (X ω) z‖) (fun _ => Υ ^ 2) :=
  fluct_avg (1 / 2) 1 (1 / 4) (fun _ => 2) 1 1 (by norm_num) one_pos (by norm_num) one_pos

end Checks

end Anisotropic

#print axioms Anisotropic.faP
#print axioms Anisotropic.faEps
#print axioms Anisotropic.faD
#print axioms Anisotropic.fluct_avg_det
#print axioms Anisotropic.taylorW
#print axioms Anisotropic.norm_taylorW_le
#print axioms Anisotropic.weight_taylor
#print axioms Anisotropic.taylorK
#print axioms Anisotropic.taylorA
#print axioms Anisotropic.faD2
#print axioms Anisotropic.fluct_avg_rand
#print axioms Anisotropic.fluct_avg
