import Anisotropic.Probability.LDE.Moment

/-!
# Large deviation estimates with deterministic coefficients

The three large deviation estimates for one row or column `x` of the matrix `X` of Section 2.1,
which the paper cites in Sections 5, 6 and 8: for deterministic complex coefficients,

* `|∑ a_i x_i| ≺ (∑|a_i|²/N)^{1/2}`;
* `|∑_{i≠j} x_i A_ij x_j| ≺ (∑_{i≠j}|A_ij|²)^{1/2}/N`;
* `|∑ a_i (x_i² - 1/N)| ≺ (∑|a_i|²)^{1/2}/N`.

Each follows from the `2p`-th moment bound of the centred family `√N x_i` (respectively
`N x_i² - 1`) by Markov's inequality, with `p = ⌈D/ε⌉ + 1`; the threshold `N₀` depends on
`(C, ε, D)` only, because the moment constants do not depend on the index set or on the
coefficients.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-! ## Markov step and the choice of the threshold -/

section Reduction

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Markov's inequality for a `2p`-th moment bound `∫ ξ^{2p} ≤ K ζ^{2p}`, with `K ≤ N^{εp}` and
`D ≤ εp`; the case `ζ = 0` is handled by the vanishing of the moment. -/
private lemma lde_markov {N : ℕ} (hN : 1 ≤ N) {ε D ζ K : ℝ} {p : ℕ} (hp1 : 1 ≤ p)
    (hp : D ≤ ε * p) (hK : K ≤ (N : ℝ) ^ (ε * p)) (hζ : 0 ≤ ζ) {ξ : Ω → ℝ}
    (hξ : ∀ ω, 0 ≤ ξ ω) (hint : Integrable fun ω => ξ ω ^ (2 * p))
    (hmom : ∫ ω, ξ ω ^ (2 * p) ≤ K * ζ ^ (2 * p)) :
    DomAt N ε D ξ (fun _ => ζ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  rcases hζ.eq_or_lt with h0 | hpos
  · have hz : ζ ^ (2 * p) = 0 := by
      rw [← h0]; exact zero_pow (by omega)
    rw [hz, mul_zero] at hmom
    have hnn : 0 ≤ ∫ ω, ξ ω ^ (2 * p) := integral_nonneg fun ω => pow_nonneg (hξ ω) _
    have hI : ∫ ω, ξ ω ^ (2 * p) = 0 := le_antisymm hmom hnn
    have hae : (fun ω => ξ ω ^ (2 * p)) =ᵐ[(ℙ : Measure Ω)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => pow_nonneg (hξ ω) _) hint).1 hI
    have hnull : (ℙ : Measure Ω) {ω | ¬ ξ ω = 0} = 0 := by
      refine ae_iff.1 ?_
      filter_upwards [hae] with ω hω
      simpa [pow_eq_zero_iff (show 2 * p ≠ 0 by omega)] using hω
    unfold DomAt
    refine le_trans (le_of_eq (measure_mono_null (fun ω hω => ?_) hnull)) zero_le
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [← h0, mul_zero] at hω
    exact hω.ne'
  · refine DomAt.of_moment (ε := ε / 2) (ε' := ε) (2 * p) hN ?_ hξ hpos hint ?_
    · push_cast; linarith
    · refine hmom.trans ?_
      have : ((N : ℝ) ^ (ε / 2) * ζ) ^ (2 * p) = (N : ℝ) ^ (ε * p) * ζ ^ (2 * p) := by
        rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)), ← Real.rpow_mul hNpos.le]
        congr 2
        push_cast
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hK (pow_nonneg hpos.le _)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Scaling: a `2p`-th moment bound for `T` transfers to `ξ = c T`. -/
private lemma lde_scale {ξ T : Ω → ℝ} {c K R ζ : ℝ} {p : ℕ} (hξT : ∀ ω, ξ ω = c * T ω)
    (hint : Integrable fun ω => T ω ^ (2 * p)) (hmom : ∫ ω, T ω ^ (2 * p) ≤ K * R)
    (hζ : ζ ^ (2 * p) = c ^ (2 * p) * R) :
    Integrable (fun ω => ξ ω ^ (2 * p)) ∧ ∫ ω, ξ ω ^ (2 * p) ≤ K * ζ ^ (2 * p) := by
  have hc : 0 ≤ c ^ (2 * p) := by rw [pow_mul]; positivity
  have h : ∀ ω, ξ ω ^ (2 * p) = c ^ (2 * p) * T ω ^ (2 * p) := fun ω => by rw [hξT, mul_pow]
  simp_rw [h]
  refine ⟨hint.const_mul _, ?_⟩
  rw [integral_const_mul, hζ]
  calc c ^ (2 * p) * ∫ ω, T ω ^ (2 * p) ≤ c ^ (2 * p) * (K * R) :=
        mul_le_mul_of_nonneg_left hmom hc
    _ = K * (c ^ (2 * p) * R) := by ring

end Reduction

/-- For `p ≥ 1` and `ε > 0`, every constant is eventually below `N^{εp}`; the threshold is at
least `1`. -/
private lemma lde_exists_N0 {ε : ℝ} (hε : 0 < ε) (K : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → K ≤ (N : ℝ) ^ (ε * p) := by
  have hexp : 0 < ε * p := mul_pos hε (by exact_mod_cast hp)
  have ht : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (ε * p)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop K)
  exact ⟨max N₁ 1, le_max_right _ _, fun N hN => hN₁ N ((le_max_left _ _).trans hN)⟩

/-- The moment order `⌈D/ε⌉ + 1` satisfies `D ≤ εp`. -/
private lemma lde_order_le {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    D ≤ ε * ((⌈D / ε⌉₊ + 1 : ℕ) : ℝ) := by
  have h1 : D / ε ≤ ⌈D / ε⌉₊ := Nat.le_ceil _
  have h2 : D ≤ ε * ⌈D / ε⌉₊ := by
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  push_cast
  nlinarith

/-! ## The three estimates -/

section LDEpins

/-- Linear large deviation estimate, deterministic coefficients:
`|∑ a_i x_i| ≺ (∑|a_i|²/N)^{1/2}`. -/
theorem lde_linear (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι : Type} [Fintype ι] (x : ι → Ω → ℝ), RowAssumption C N x → ∀ a : ι → ℂ,
      DomAt N ε D (fun ω => ‖∑ i, a i * x i ω‖) (fun _ => ldeLinBound N a) := by
  obtain ⟨N₀, hN₀, hN⟩ := lde_exists_N0 hε (ldeLinConst C (⌈D / ε⌉₊ + 1)) (p := ⌈D / ε⌉₊ + 1)
    (by omega)
  refine ⟨N₀, ?_⟩
  intro N hNN Ω _ _ ι _ x hx a
  set p := ⌈D / ε⌉₊ + 1 with hpdef
  have hN1 : 1 ≤ N := hN₀.trans hNN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hI, hM⟩ := lde_lin_moment hx.centredMoments a p
  have hs : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : ∀ ω, ‖∑ i, a i * (x i ω : ℂ)‖ =
      (Real.sqrt N)⁻¹ * ‖∑ i, a i * ((Real.sqrt N * x i ω : ℝ) : ℂ)‖ := by
    intro ω
    have h : ∑ i, a i * ((Real.sqrt N * x i ω : ℝ) : ℂ) =
        (Real.sqrt N : ℂ) * ∑ i, a i * (x i ω : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    have hr : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    field_simp
  have hζ : ldeLinBound N a ^ (2 * p) = ((Real.sqrt N)⁻¹) ^ (2 * p) * (∑ i, ‖a i‖ ^ 2) ^ p := by
    unfold ldeLinBound
    rw [pow_mul, pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), inv_pow,
      Real.sq_sqrt hNpos.le, ← mul_pow, ← Finset.sum_div, inv_mul_eq_div, div_eq_mul_inv,
      mul_comm]
  have := lde_scale (ξ := fun ω => ‖∑ i, a i * (x i ω : ℂ)‖)
    (T := fun ω => ‖∑ i, a i * ((Real.sqrt N * x i ω : ℝ) : ℂ)‖) hsq hI hM hζ
  exact lde_markov hN1 (by omega) (lde_order_le hε D) (hN N hNN) (Real.sqrt_nonneg _)
    (fun ω => norm_nonneg _) this.1 this.2

/-- Off-diagonal quadratic large deviation estimate, deterministic coefficients:
`|∑_{i≠j} x_i A_ij x_j| ≺ (∑_{i≠j}|A_ij|²)^{1/2}/N`. -/
theorem lde_offdiag (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → Ω → ℝ), RowAssumption C N x →
      ∀ A : ι → ι → ℂ,
      DomAt N ε D (fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i, x i ω * A i j * x j ω‖)
        (fun _ => ldeOffBound N A) := by
  obtain ⟨N₀, hN₀, hN⟩ := lde_exists_N0 hε (ldeOffConst C (⌈D / ε⌉₊ + 1)) (p := ⌈D / ε⌉₊ + 1)
    (by omega)
  refine ⟨N₀, ?_⟩
  intro N hNN Ω _ _ ι _ _ x hx A
  set p := ⌈D / ε⌉₊ + 1 with hpdef
  have hN1 : 1 ≤ N := hN₀.trans hNN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hI, hM⟩ := lde_off_moment hx.centredMoments A p
  have hsq : ∀ ω, ‖∑ i, ∑ j ∈ Finset.univ.erase i, (x i ω : ℂ) * A i j * (x j ω : ℂ)‖ =
      (N : ℝ)⁻¹ * ‖∑ i, ∑ j ∈ Finset.univ.erase i,
        ((Real.sqrt N * x i ω : ℝ) : ℂ) * A i j * ((Real.sqrt N * x j ω : ℝ) : ℂ)‖ := by
    intro ω
    have hss : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNpos.le]
      simp
    have h : ∑ i, ∑ j ∈ Finset.univ.erase i,
        ((Real.sqrt N * x i ω : ℝ) : ℂ) * A i j * ((Real.sqrt N * x j ω : ℝ) : ℂ) =
        (N : ℂ) * ∑ i, ∑ j ∈ Finset.univ.erase i, (x i ω : ℂ) * A i j * (x j ω : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      linear_combination ((x i ω : ℂ) * A i j * (x j ω : ℂ)) * hss
    rw [h, norm_mul, Complex.norm_natCast]
    field_simp
  have hS : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hζ : ldeOffBound N A ^ (2 * p) =
      ((N : ℝ)⁻¹) ^ (2 * p) * (∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2) ^ p := by
    unfold ldeOffBound
    rw [pow_mul, pow_mul, div_pow, Real.sq_sqrt hS, inv_pow, ← mul_pow, div_eq_mul_inv,
      mul_comm]
  have := lde_scale (ξ := fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i,
      (x i ω : ℂ) * A i j * (x j ω : ℂ)‖)
    (T := fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i,
      ((Real.sqrt N * x i ω : ℝ) : ℂ) * A i j * ((Real.sqrt N * x j ω : ℝ) : ℂ)‖)
    hsq hI hM hζ
  exact lde_markov hN1 (by omega) (lde_order_le hε D) (hN N hNN)
    (div_nonneg (Real.sqrt_nonneg _) hNpos.le) (fun ω => norm_nonneg _) this.1 this.2

/-- Diagonal large deviation estimate, deterministic coefficients:
`|∑ a_i (x_i² - 1/N)| ≺ (∑|a_i|²)^{1/2}/N`. -/
theorem lde_diag (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι : Type} [Fintype ι] (x : ι → Ω → ℝ), RowAssumption C N x → ∀ a : ι → ℂ,
      DomAt N ε D (fun ω => ‖∑ i, a i * (x i ω ^ 2 - 1 / (N : ℝ))‖)
        (fun _ => ldeDiagBound N a) := by
  obtain ⟨N₀, hN₀, hN⟩ := lde_exists_N0 hε (ldeLinConst (diagMoments C) (⌈D / ε⌉₊ + 1))
    (p := ⌈D / ε⌉₊ + 1) (by omega)
  refine ⟨N₀, ?_⟩
  intro N hNN Ω _ _ ι _ x hx a
  set p := ⌈D / ε⌉₊ + 1 with hpdef
  have hN1 : 1 ≤ N := hN₀.trans hNN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hI, hM⟩ := lde_lin_moment (hx.centredMoments_sq hN1) a p
  have hsq : ∀ ω, ‖∑ i, a i * ((x i ω : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖ =
      (N : ℝ)⁻¹ * ‖∑ i, a i * (((N : ℝ) * x i ω ^ 2 - 1 : ℝ) : ℂ)‖ := by
    intro ω
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN1.trans_lt' Nat.zero_lt_one |>.ne'
    have h : ∑ i, a i * (((N : ℝ) * x i ω ^ 2 - 1 : ℝ) : ℂ) =
        (N : ℂ) * ∑ i, a i * ((x i ω : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      field_simp
    rw [h, norm_mul, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
  have hS : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hζ : ldeDiagBound N a ^ (2 * p) = ((N : ℝ)⁻¹) ^ (2 * p) * (∑ i, ‖a i‖ ^ 2) ^ p := by
    unfold ldeDiagBound
    rw [pow_mul, pow_mul, div_pow, Real.sq_sqrt hS, inv_pow, ← mul_pow, div_eq_mul_inv,
      mul_comm]
  have := lde_scale (ξ := fun ω => ‖∑ i, a i * ((x i ω : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖)
    (T := fun ω => ‖∑ i, a i * (((N : ℝ) * x i ω ^ 2 - 1 : ℝ) : ℂ)‖) hsq hI hM hζ
  exact lde_markov hN1 (by omega) (lde_order_le hε D) (hN N hNN)
    (div_nonneg (Real.sqrt_nonneg _) hNpos.le) (fun ω => norm_nonneg _) this.1 this.2

end LDEpins

end Anisotropic
