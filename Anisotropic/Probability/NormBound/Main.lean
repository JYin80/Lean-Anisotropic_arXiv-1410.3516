module

public import Anisotropic.Probability.NormBound.TraceMoment
public import Anisotropic.Probability.NormBound.Truncation

@[expose] public section

/-!
# The bound `‖XᵀX‖ ≤ C₀` with high probability

Lemma 4.8 (`lem:norm_XX`): for a `K × N` matrix `X` with the entry conditions of Assumption 2.1
and `K ≤ τ⁻¹ N`, `‖XᵀX‖ ≤ C₀` with high probability, with `C₀ = (1 + √(18/τ))²` depending on `τ`
only; and the variant with the entry `(i, μ)` replaced by `y`, `|y| ≤ 1` with high probability,
used in the proof of Lemma 7.14.

Proof of Lemma 4.8: truncate the entries at `N^{-1/4}` (`X̂ = X` with high probability), write
`X̂ = Y + E X̂` with `Y` centred, `|Y| ≤ 2 N^{-1/4}` and `E X̂` negligible, and apply Markov's
inequality to `tr (Y Yᵀ)^k` with `k = (⌈D⌉₊ + 2)(⌊log₂ N⌋ + 1)` and level `(18/τ)^k`. For the
variant, `‖X'‖ ≤ ‖X‖ + |y| + |X_{iμ}|` where `X'` is the updated matrix.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-- The matrix `A` with entry `(i, μ)` replaced by `t`. -/
def updEntry {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) (i : Fin K) (μ : Fin N) (t : ℝ) :
    Matrix (Fin K) (Fin N) ℝ :=
  A.updateRow i (Function.update (A i) μ t)

/-! ## Operator norm bounds -/

/-- `‖Aᵀ A‖ = ‖A‖²` for a real matrix. -/
private lemma normMain_transpose_mul_self {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) :
    ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
  simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose_mul_self A

/-- `‖A Aᵀ‖ = ‖A‖²` for a real matrix. -/
private lemma normMain_mul_transpose_self {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) :
    ‖A * Aᵀ‖ = ‖A‖ * ‖A‖ := by
  have h := normMain_transpose_mul_self Aᵀ
  have ht : ‖Aᵀ‖ = ‖A‖ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose A
  rw [transpose_transpose, ht] at h
  exact h

/-- The matrix with the single entry `c` at `(i, μ)` has operator norm `|c|`. -/
private lemma normMain_norm_single {K N : ℕ} (i : Fin K) (μ : Fin N) (c : ℝ) :
    ‖(single i μ c : Matrix (Fin K) (Fin N) ℝ)‖ = |c| := by
  have h := normMain_transpose_mul_self (single i μ c)
  rw [transpose_single, single_mul_single_same, ← diagonal_single, l2_opNorm_diagonal,
    Pi.norm_single, Real.norm_eq_abs, abs_mul] at h
  exact (mul_self_inj (norm_nonneg _) (abs_nonneg c)).1 h.symm

/-- The operator norm is at most the sum of the absolute values of the entries. -/
private lemma normMain_norm_le_sum {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) :
    ‖A‖ ≤ ∑ i, ∑ μ, |A i μ| := by
  calc ‖A‖ = ‖∑ i, ∑ μ, single i μ (A i μ)‖ := by rw [← matrix_eq_sum_single]
    _ ≤ ∑ i, ‖∑ μ, single i μ (A i μ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ μ, ‖single i μ (A i μ)‖ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ = ∑ i, ∑ μ, |A i μ| := by simp only [normMain_norm_single]

/-- `updEntry A i μ t = A + (t - A_{iμ}) E_{iμ}`. -/
private lemma normMain_updEntry_eq {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) (i : Fin K)
    (μ : Fin N) (t : ℝ) : updEntry A i μ t = A + single i μ (t - A i μ) := by
  ext i' μ'
  simp only [updEntry, updateRow_apply, Function.update_apply, Matrix.add_apply, single_apply]
  by_cases h1 : i' = i <;> by_cases h2 : μ' = μ
  · subst h1; subst h2; simp
  · simp [h1, h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]
  · simp [h1, Ne.symm h1]

/-- `‖updEntry A i μ t‖ ≤ ‖A‖ + |t| + |A_{iμ}|`. -/
private lemma normMain_norm_updEntry_le {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) (i : Fin K)
    (μ : Fin N) (t : ℝ) : ‖updEntry A i μ t‖ ≤ ‖A‖ + |t| + |A i μ| := by
  rw [normMain_updEntry_eq]
  calc ‖A + single i μ (t - A i μ)‖ ≤ ‖A‖ + ‖single i μ (t - A i μ)‖ := norm_add_le _ _
    _ = ‖A‖ + |t - A i μ| := by rw [normMain_norm_single]
    _ ≤ ‖A‖ + |t| + |A i μ| := by linarith [abs_sub t (A i μ)]

/-! ## The choice of `k` -/

/-- `c (m + 1)^12 ≤ 2^m` for all large `m`. -/
private lemma normMain_pow_two (c : ℝ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, c * ((m : ℝ) + 1) ^ 12 ≤ 2 ^ m := by
  have h := (Filter.tendsto_add_atTop_iff_nat 1).2
    (tendsto_pow_const_div_const_pow_of_one_lt 12 (r := 2) one_lt_two)
  have hε : (0 : ℝ) < 1 / (2 * (|c| + 1)) := by positivity
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hε))
  refine ⟨m₀, fun m hm => ?_⟩
  have h1 := hm₀ m hm
  push_cast at h1
  rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_succ (2 : ℝ) m] at h1
  have h2 : c * ((m : ℝ) + 1) ^ 12 ≤ (|c| + 1) * ((m : ℝ) + 1) ^ 12 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) (by positivity)
  have h3 : (0 : ℝ) ≤ (|c| + 1) * ((m : ℝ) + 1) ^ 12 := by positivity
  nlinarith

/-! ## The moment method at fixed `N` -/

section E1

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- At fixed `N` and `k`, with `δ = 1/4`: if `2 (2k)^6 b² ≤ 1` for `b = 2 N^{-1/4}` and the means
of the truncated entries sum to at most `1` in absolute value, then the event
`{‖XᵀX‖ ≤ (1 + √(18/τ))², all |X_{iμ}| ≤ 1}` fails with probability at most
`K N C_q N^{-q/4} + 2 τ⁻¹ N 2^{-k}`. -/
private lemma normMain_core {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {C : ℕ → ℝ} {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) (q : ℕ) {K : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hK : (K : ℝ) ≤ τ⁻¹ * N)
    (hsmall : 2 * ((2 * k : ℕ) : ℝ) ^ 6 * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ) + 1 / 4)) ^ 2 ≤ 1)
    (hM : ∑ i, ∑ μ, |∫ ω, truncX (1 / 4) X ω i μ| ≤ 1) :
    ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt (18 / τ)) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1}ᶜ ≤
      ENNReal.ofReal (K * N * C q * (N : ℝ) ^ (-(q * (1 / 4 : ℝ)))) +
        ENNReal.ofReal (2 * τ⁻¹ * N * (1 / 2) ^ k) := by
  classical
  set t : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ) + 1 / 4) with ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htpos : 0 < t := Real.rpow_pos_of_pos hNpos _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  set h0 : ℝ → ℝ := fun x => if |x| ≤ t then x else 0 with hh0
  have hh0m : Measurable h0 :=
    Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
      measurable_const
  have hh0bd : ∀ x, |h0 x| ≤ t := by
    intro x
    simp only [hh0]
    split_ifs with h
    · exact h
    · simp [htpos.le]
  set Xh := truncX (1 / 4) X with hXh
  have hXh_eq : ∀ ω i μ, Xh ω i μ = h0 (X ω i μ) := fun _ _ _ => rfl
  have hXhm : ∀ i μ, Measurable fun ω => Xh ω i μ := fun i μ => hh0m.comp (hX.measurable i μ)
  have hXh_int : ∀ i μ, Integrable fun ω => Xh ω i μ := fun i μ =>
    Integrable.of_bound (hXhm i μ).aestronglyMeasurable t
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, hXh_eq]; exact hh0bd _)
  set M : Matrix (Fin K) (Fin N) ℝ := fun i μ => ∫ ω, Xh ω i μ with hM_def
  have hM_bd : ∀ i μ, |M i μ| ≤ t := by
    intro i μ
    have := norm_integral_le_of_norm_le_const (μ := ℙ) (f := fun ω => Xh ω i μ) (C := t)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, hXh_eq]; exact hh0bd _)
    simpa using this
  set g : Fin K × Fin N → ℝ → ℝ := fun p x => h0 x - M p.1 p.2 with hg
  have hgm : ∀ p, Measurable (g p) := fun p => hh0m.sub_const _
  set Y : Ω → Matrix (Fin K) (Fin N) ℝ := fun ω i μ => g (i, μ) (X ω i μ) with hY
  have hY_eq : ∀ ω i μ, Y ω i μ = Xh ω i μ - M i μ := fun _ _ _ => rfl
  have hYm : ∀ i μ, Measurable fun ω => Y ω i μ := fun i μ => (hgm (i, μ)).comp (hX.measurable i μ)
  have hYind : iIndepFun (fun (p : Fin K × Fin N) ω => Y ω p.1 p.2) ℙ := hX.indep.comp g hgm
  have hYmean : ∀ i μ, ∫ ω, Y ω i μ = 0 := by
    intro i μ
    simp only [hY_eq]
    rw [integral_sub (hXh_int i μ) (integrable_const _)]
    simp [hM_def]
  have hX2int : ∀ i μ, Integrable fun ω => X ω i μ ^ 2 := by
    intro i μ
    have h := (hX.integrable_moment 2 i μ).const_mul ((N : ℝ)⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [sq_abs, mul_pow, Real.sq_sqrt hNpos.le]
    field_simp
  have hYvar : ∀ i μ, ∫ ω, Y ω i μ ^ 2 ≤ 1 / (N : ℝ) := by
    intro i μ
    have hexp : (fun ω => Y ω i μ ^ 2) =
        fun ω => (Xh ω i μ ^ 2 - 2 * M i μ * Xh ω i μ) + M i μ ^ 2 := by
      funext ω
      rw [hY_eq]
      ring
    have hXh2int : Integrable fun ω => Xh ω i μ ^ 2 :=
      Integrable.of_bound ((hXhm i μ).pow_const 2).aestronglyMeasurable (t ^ 2)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_pow, hXh_eq]
          exact pow_le_pow_left₀ (abs_nonneg _) (hh0bd _) 2)
    have h1 : ∫ ω, Xh ω i μ ^ 2 ≤ ∫ ω, X ω i μ ^ 2 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) (hX2int i μ)
        (Filter.Eventually.of_forall fun ω => by
          simp only [hXh_eq, hh0]
          split_ifs
          · exact le_rfl
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            positivity)
    rw [hX.var] at h1
    rw [hexp, integral_add (f := fun ω => Xh ω i μ ^ 2 - 2 * M i μ * Xh ω i μ)
      (g := fun _ => M i μ ^ 2) (hXh2int.sub ((hXh_int i μ).const_mul _)) (integrable_const _),
      integral_sub (f := fun ω => Xh ω i μ ^ 2) (g := fun ω => 2 * M i μ * Xh ω i μ) hXh2int
        ((hXh_int i μ).const_mul _), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    have : ∫ ω, Xh ω i μ = M i μ := rfl
    rw [this]
    nlinarith [sq_nonneg (M i μ)]
  set b : ℝ := 2 * t with hb
  have hYbd : ∀ ω i μ, |Y ω i μ| ≤ b := by
    intro ω i μ
    rw [hY_eq, hXh_eq]
    calc |h0 (X ω i μ) - M i μ| ≤ |h0 (X ω i μ)| + |M i μ| := abs_sub _ _
      _ ≤ t + t := add_le_add (hh0bd _) (hM_bd i μ)
      _ = b := by ring
  have ht2 : t ^ 2 * N = Real.sqrt N := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, Real.sqrt_eq_rpow]
    conv_lhs => rhs; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNpos]
    norm_num
  have hsqrt1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  have hbN : 1 ≤ b ^ 2 * N := by
    have : b ^ 2 * N = 4 * (t ^ 2 * N) := by rw [hb]; ring
    rw [this, ht2]
    linarith
  have hE := integral_trace_pow_le hτ hτ1 hk hK Y hYm hYind hYmean hYvar hYbd hbN hsmall
  -- integrability of the trace, through the walk expansion
  set f : Ω → ℝ := fun ω => trace ((Y ω * (Y ω)ᵀ) ^ k) with hf
  have hfint : Integrable f := by
    have hpt : f = fun ω => ∑ i : Fin k → Fin K, ∑ μ : Fin k → Fin N,
        ∏ s, Y ω (i s) (μ s) * Y ω (i (finRotate k s)) (μ s) :=
      funext fun ω => trace_pow_eq_sum_walks hk (Y ω)
    rw [hpt]
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun μ _ =>
      Integrable.of_bound
        (Finset.measurable_prod _ fun s _ => (hYm _ _).mul (hYm _ _)).aestronglyMeasurable
        (∏ _s : Fin k, b * b)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, Finset.abs_prod]
          exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun s _ => by
            rw [abs_mul]
            exact mul_le_mul (hYbd _ _ _) (hYbd _ _ _) (abs_nonneg _) hb0)
  have hfge : ∀ ω, ‖Y ω * (Y ω)ᵀ‖ ^ k ≤ f ω := fun ω => opNorm_pow_le_trace (Y ω) hk
  -- Markov's inequality at level `L^k`
  set L : ℝ := 18 / τ with hL
  have hLpos : 0 < L := by positivity
  have hMk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (pow_nonneg (norm_nonneg _) k).trans (hfge ω)) hfint
    (L ^ k)
  have hLk : 2 * τ⁻¹ * (9 / τ) ^ k * N = L ^ k * (2 * τ⁻¹ * N * (1 / 2) ^ k) := by
    have h9 : 9 / τ = L * (1 / 2) := by rw [hL]; ring
    rw [h9, mul_pow]
    ring
  have hPreal : (ℙ : Measure Ω).real {ω | L ^ k ≤ f ω} ≤ 2 * τ⁻¹ * N * (1 / 2) ^ k := by
    have h := hMk.trans (hE.trans_eq hLk)
    exact le_of_mul_le_mul_left h (pow_pos hLpos k)
  have hP : ℙ {ω | L ^ k ≤ f ω} ≤ ENNReal.ofReal (2 * τ⁻¹ * N * (1 / 2) ^ k) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hPreal
  -- the deterministic inclusion
  have hsub : {ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt (18 / τ)) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1}ᶜ ⊆
      {ω | Xh ω ≠ X ω} ∪ {ω | L ^ k ≤ f ω} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, ne_eq, not_not, not_le] at hcon
    obtain ⟨hXX, hlt⟩ := hcon
    apply hω
    have hXent : ∀ i μ, Xh ω i μ = X ω i μ := fun i μ => by rw [hXX]
    have hdec : X ω = Y ω + M := by
      ext i μ
      rw [Matrix.add_apply, hY_eq, hXent]
      ring
    have hYY : ‖Y ω * (Y ω)ᵀ‖ < L := by
      by_contra h
      exact absurd ((pow_le_pow_left₀ hLpos.le (not_lt.1 h) k).trans (hfge ω)) (not_le.2 hlt)
    rw [normMain_mul_transpose_self] at hYY
    have hYn : ‖Y ω‖ ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by nlinarith)
    have hMn : ‖M‖ ≤ 1 := (normMain_norm_le_sum M).trans hM
    have hXn : ‖X ω‖ ≤ 1 + Real.sqrt L := by
      rw [hdec]
      linarith [norm_add_le (Y ω) M]
    refine ⟨?_, fun i μ => ?_⟩
    · rw [normMain_transpose_mul_self, ← hL, sq]
      exact mul_self_le_mul_self (norm_nonneg _) hXn
    · rw [← hXent, hXh_eq]
      exact (hh0bd _).trans ht1
  calc ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt (18 / τ)) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1}ᶜ
      ≤ ℙ ({ω | Xh ω ≠ X ω} ∪ {ω | L ^ k ≤ f ω}) := measure_mono hsub
    _ ≤ ℙ {ω | Xh ω ≠ X ω} + ℙ {ω | L ^ k ≤ f ω} := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_truncX_ne_le hX hN (1 / 4) q) hP

/-! ## Lemma 4.8 -/

/-- The event of Lemma 4.8 with `C₀ = (1 + √(18/τ))²`, together with `|X_{iμ}| ≤ 1` for all
entries, holds with high probability. -/
private lemma normMain_highProb {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (C : ℕ → ℝ) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (K : ℕ) (X : Ω → Matrix (Fin K) (Fin N) ℝ), EntryAssumption C X →
      (K : ℝ) ≤ τ⁻¹ * N → HighProbAt N D
        {ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt (18 / τ)) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1} := by
  set D' : ℕ := ⌈D⌉₊ with hD'
  set q : ℕ := 4 * D' + 12 with hq
  set Cq : ℝ := max (C q) 0 with hCq
  set a : ℕ := D' + 2 with ha
  obtain ⟨m₀, hm₀⟩ := normMain_pow_two (64 * (2 * (a : ℝ)) ^ 12)
  refine ⟨max (2 ^ m₀) (⌈τ⁻¹ * (Cq + 2)⌉₊ + 1), fun N hN => ?_⟩
  intro Ω _ _ K X hX hK
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow (le_of_max_le_left hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNbig : τ⁻¹ * (Cq + 2) ≤ N := by
    have h1 := Nat.le_ceil (τ⁻¹ * (Cq + 2))
    have h2 : ⌈τ⁻¹ * (Cq + 2)⌉₊ + 1 ≤ N := le_of_max_le_right hN
    have h3 : ((⌈τ⁻¹ * (Cq + 2)⌉₊ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast h2
    linarith
  have hCq0 : 0 ≤ Cq := le_max_right _ _
  have hCCq : C q ≤ Cq := le_max_left _ _
  have hDD' : D ≤ D' := Nat.le_ceil D
  have hτinv : 0 < τ⁻¹ := inv_pos.2 hτ
  set m := Nat.log 2 N with hm
  set k := a * (m + 1) with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hmm : m₀ ≤ m := Nat.le_log_of_pow_le one_lt_two (le_of_max_le_left hN)
  have h2m : 2 ^ m ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hNk : N ^ a < 2 ^ k := by
    rw [hk, mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self one_lt_two N) (by positivity)
  -- the condition `2 (2k)^6 b² ≤ 1` of the trace moment bound
  have hsmall : 2 * ((2 * k : ℕ) : ℝ) ^ 6 * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ) + 1 / 4)) ^ 2 ≤ 1 := by
    have hc := hm₀ m hmm
    have hx : 64 * ((2 * k : ℕ) : ℝ) ^ 12 ≤ N := by
      have h2m' : ((2 ^ m : ℕ) : ℝ) ≤ N := by exact_mod_cast h2m
      rw [hk]
      push_cast at h2m' ⊢
      calc 64 * (2 * ((a : ℝ) * ((m : ℝ) + 1))) ^ 12
          = 64 * (2 * (a : ℝ)) ^ 12 * ((m : ℝ) + 1) ^ 12 := by ring
        _ ≤ 2 ^ m := hc
        _ ≤ N := h2m'
    have hsq : 8 * ((2 * k : ℕ) : ℝ) ^ 6 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
    have ht2 : ((N : ℝ) ^ (-(1 / 2 : ℝ) + 1 / 4)) ^ 2 = (Real.sqrt N)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, Real.sqrt_eq_rpow,
        ← Real.rpow_neg hNpos.le]
      norm_num
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
    rw [mul_pow, ht2]
    rw [show 2 * ((2 * k : ℕ) : ℝ) ^ 6 * (2 ^ 2 * (Real.sqrt N)⁻¹) =
      8 * ((2 * k : ℕ) : ℝ) ^ 6 / Real.sqrt N by ring]
    rw [div_le_one hs]
    exact hsq
  -- the means of the truncated entries
  have hM : ∑ i, ∑ μ, |∫ ω, truncX (1 / 4) X ω i μ| ≤ 1 := by
    have hq1 : 1 ≤ q := by omega
    have hterm : ∀ i μ, |∫ ω, truncX (1 / 4) X ω i μ| ≤ Cq * (N : ℝ) ^ (-3 : ℝ) := by
      intro i μ
      refine (abs_integral_truncX_le hX hN1 (1 / 4) hq1 i μ).trans ?_
      have he : (N : ℝ) ^ (-(1 / 2 : ℝ) - 1 / 4 * ((q : ℝ) - 1)) ≤ (N : ℝ) ^ (-3 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1r
        rw [hq]
        push_cast
        have : (0 : ℝ) ≤ D' := Nat.cast_nonneg _
        linarith
      exact mul_le_mul hCCq he (Real.rpow_nonneg hNpos.le _) hCq0
    have hsum : ∑ i : Fin K, ∑ μ : Fin N, |∫ ω, truncX (1 / 4) X ω i μ| ≤
        K * (N * (Cq * (N : ℝ) ^ (-3 : ℝ))) := by
      calc ∑ i : Fin K, ∑ μ : Fin N, |∫ ω, truncX (1 / 4) X ω i μ|
          ≤ ∑ _i : Fin K, ∑ _μ : Fin N, Cq * (N : ℝ) ^ (-3 : ℝ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hterm i μ
        _ = K * (N * (Cq * (N : ℝ) ^ (-3 : ℝ))) := by simp
    refine hsum.trans ?_
    have hN3 : (N : ℝ) ^ (-3 : ℝ) = ((N : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hNpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hN3]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    calc (K : ℝ) * (N * (Cq * ((N : ℝ) ^ 3)⁻¹))
        ≤ τ⁻¹ * N * (N * (Cq * ((N : ℝ) ^ 3)⁻¹)) :=
          mul_le_mul_of_nonneg_right hK (by positivity)
      _ = τ⁻¹ * Cq / N := by field_simp
      _ ≤ 1 := by
          rw [div_le_one hNpos]
          nlinarith
  have hcore := normMain_core hτ hτ1 hN1 hk1 q hX hK hsmall hM
  -- the two error terms
  set P : ℝ := (N : ℝ) ^ (-D) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNpos.le _
  have hy1 : (K : ℝ) * N * C q * (N : ℝ) ^ (-(q * (1 / 4 : ℝ))) ≤ τ⁻¹ * Cq * (P / N) := by
    have hz : (N : ℝ) * N * (N : ℝ) ^ (-(q * (1 / 4 : ℝ))) ≤ P / N := by
      rw [hP, ← Real.rpow_sub_one hNpos.ne',
        show (N : ℝ) * N * (N : ℝ) ^ (-(q * (1 / 4 : ℝ))) =
          (N : ℝ) ^ ((1 : ℝ) + 1 + -(q * (1 / 4 : ℝ))) by
          rw [Real.rpow_add hNpos, Real.rpow_add hNpos, Real.rpow_one]]
      apply Real.rpow_le_rpow_of_exponent_le hN1r
      rw [hq]
      push_cast
      linarith
    have hw0 : 0 ≤ (N : ℝ) ^ (-(q * (1 / 4 : ℝ))) := Real.rpow_nonneg hNpos.le _
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    calc (K : ℝ) * N * C q * (N : ℝ) ^ (-(q * (1 / 4 : ℝ)))
        ≤ K * N * Cq * (N : ℝ) ^ (-(q * (1 / 4 : ℝ))) := by gcongr
      _ ≤ τ⁻¹ * N * N * Cq * (N : ℝ) ^ (-(q * (1 / 4 : ℝ))) := by gcongr
      _ = τ⁻¹ * Cq * ((N : ℝ) * N * (N : ℝ) ^ (-(q * (1 / 4 : ℝ)))) := by ring
      _ ≤ τ⁻¹ * Cq * (P / N) := by gcongr
  have hy2 : 2 * τ⁻¹ * N * (1 / 2 : ℝ) ^ k ≤ 2 * τ⁻¹ * (P / N) := by
    have hNk' : ((N : ℝ) ^ a) ≤ (2 : ℝ) ^ k := by exact_mod_cast hNk.le
    have hNa : 0 < (N : ℝ) ^ a := by positivity
    have h1 : (1 / 2 : ℝ) ^ k ≤ ((N : ℝ) ^ a)⁻¹ := by
      rw [_root_.one_div_pow]
      rw [← one_div]
      exact one_div_le_one_div_of_le hNa hNk'
    have h2 : (N : ℝ) * ((N : ℝ) ^ a)⁻¹ ≤ P / N := by
      rw [hP, ← Real.rpow_sub_one hNpos.ne', ← Real.rpow_natCast,
        ← Real.rpow_neg hNpos.le, ← Real.rpow_one_add' hNpos.le]
      · apply Real.rpow_le_rpow_of_exponent_le hN1r
        rw [ha]
        push_cast
        linarith
      · rw [ha]
        push_cast
        have : (0 : ℝ) ≤ D' := Nat.cast_nonneg _
        linarith
    calc 2 * τ⁻¹ * N * (1 / 2 : ℝ) ^ k ≤ 2 * τ⁻¹ * N * ((N : ℝ) ^ a)⁻¹ := by gcongr
      _ = 2 * τ⁻¹ * ((N : ℝ) * ((N : ℝ) ^ a)⁻¹) := by ring
      _ ≤ 2 * τ⁻¹ * (P / N) := by gcongr
  unfold HighProbAt
  refine hcore.trans ?_
  calc ENNReal.ofReal (K * N * C q * (N : ℝ) ^ (-(q * (1 / 4 : ℝ)))) +
        ENNReal.ofReal (2 * τ⁻¹ * N * (1 / 2) ^ k)
      ≤ ENNReal.ofReal (τ⁻¹ * Cq * (P / N)) + ENNReal.ofReal (2 * τ⁻¹ * (P / N)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hy1) (ENNReal.ofReal_le_ofReal hy2)
    _ = ENNReal.ofReal (τ⁻¹ * (Cq + 2) * (P / N)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal P := by
        apply ENNReal.ofReal_le_ofReal
        calc τ⁻¹ * (Cq + 2) * (P / N) ≤ N * (P / N) := by gcongr
          _ = P := by field_simp

/-- Lemma 4.8 (`lem:norm_XX`): `‖XᵀX‖ ≤ C₀` with high probability, `C₀` depending on `τ` only,
for every `K × N` matrix with the entry conditions and `K ≤ τ⁻¹ N`. -/
theorem norm_XtX_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ C₀ : ℝ, ∀ (C : ℕ → ℝ) (D : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (K : ℕ) (X : Ω → Matrix (Fin K) (Fin N) ℝ), EntryAssumption C X →
      (K : ℝ) ≤ τ⁻¹ * N → HighProbAt N D {ω | ‖(X ω)ᵀ * X ω‖ ≤ C₀} := by
  refine ⟨(1 + Real.sqrt (18 / τ)) ^ 2, fun C D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := normMain_highProb hτ hτ1 C D
  refine ⟨N₀, fun N hN => ?_⟩
  intro Ω _ _ K X hX hK
  have h := hN₀ N hN K X hX hK
  unfold HighProbAt at h ⊢
  refine le_trans (measure_mono ?_) h
  exact Set.compl_subset_compl.2 fun ω hω => hω.1

/-- Variant used in the proof of Lemma 7.14: one entry replaced by `y` with
`|y| ≤ 1` with high probability. -/
theorem norm_XtX_updEntry_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ C₁ : ℝ, ∀ (C : ℕ → ℝ) (D : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (K : ℕ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (i : Fin K) (μ : Fin N) (y : Ω → ℝ),
      EntryAssumption C X → (K : ℝ) ≤ τ⁻¹ * N → HighProbAt N (D + 1) {ω | |y ω| ≤ 1} →
      HighProbAt N D {ω | ‖(updEntry (X ω) i μ (y ω))ᵀ * updEntry (X ω) i μ (y ω)‖ ≤ C₁} := by
  refine ⟨(3 + Real.sqrt (18 / τ)) ^ 2, fun C D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := normMain_highProb hτ hτ1 C (D + 1)
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  intro Ω _ _ K X i μ y hX hK hy
  have hA := hN₀ N (le_of_max_le_left hN) K X hX hK
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold HighProbAt at hA hy ⊢
  set L : ℝ := 18 / τ with hL
  have hsub : {ω | ‖(updEntry (X ω) i μ (y ω))ᵀ * updEntry (X ω) i μ (y ω)‖ ≤
        (3 + Real.sqrt L) ^ 2}ᶜ ⊆
      {ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt L) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1}ᶜ ∪
        {ω | |y ω| ≤ 1}ᶜ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq] at hcon
    obtain ⟨⟨hXX, hent⟩, hyω⟩ := hcon
    apply hω
    have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hXn : ‖X ω‖ ≤ 1 + Real.sqrt L := by
      rw [normMain_transpose_mul_self] at hXX
      have := Real.sqrt_le_sqrt hXX
      rwa [Real.sqrt_mul_self (norm_nonneg _), Real.sqrt_sq (by positivity)] at this
    have hU : ‖updEntry (X ω) i μ (y ω)‖ ≤ 3 + Real.sqrt L := by
      linarith [normMain_norm_updEntry_le (X ω) i μ (y ω), hent i μ]
    change ‖(updEntry (X ω) i μ (y ω))ᵀ * updEntry (X ω) i μ (y ω)‖ ≤ (3 + Real.sqrt L) ^ 2
    rw [normMain_transpose_mul_self, sq]
    exact mul_self_le_mul_self (norm_nonneg _) hU
  have hP0 : 0 ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  calc ℙ {ω | ‖(updEntry (X ω) i μ (y ω))ᵀ * updEntry (X ω) i μ (y ω)‖ ≤
        (3 + Real.sqrt L) ^ 2}ᶜ
      ≤ ℙ ({ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt L) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1}ᶜ ∪
        {ω | |y ω| ≤ 1}ᶜ) := measure_mono hsub
    _ ≤ ℙ {ω | ‖(X ω)ᵀ * X ω‖ ≤ (1 + Real.sqrt L) ^ 2 ∧ ∀ i μ, |X ω i μ| ≤ 1}ᶜ +
        ℙ {ω | |y ω| ≤ 1}ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hA hy
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hP0 hP0]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show -(D + 1) = -D - 1 by ring, Real.rpow_sub_one hNpos.ne']
        have hP : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hNpos.le _
        rw [mul_div_assoc', div_le_iff₀ hNpos]
        nlinarith

end E1

end Anisotropic

#print axioms Anisotropic.updEntry
#print axioms Anisotropic.norm_XtX_le
#print axioms Anisotropic.norm_XtX_updEntry_le
