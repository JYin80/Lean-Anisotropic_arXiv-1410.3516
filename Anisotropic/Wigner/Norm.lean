import Anisotropic.Framework.Domination
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Probability.NormBound.TraceMoment
import Anisotropic.Wigner.GOE
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.NormTrunc

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The norm bound `‖W‖ ≤ C₀` with high probability for the class of entry laws -/

/-! ## Operator norm bounds -/

/-- `‖Aᵀ A‖ = ‖A‖²` for a real matrix. -/
private lemma aux_transpose_mul_self {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) :
    ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
  simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose_mul_self A

/-- `‖A Aᵀ‖ = ‖A‖²` for a real matrix. -/
private lemma aux_mul_transpose_self {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) :
    ‖A * Aᵀ‖ = ‖A‖ * ‖A‖ := by
  have h := aux_transpose_mul_self Aᵀ
  have ht : ‖Aᵀ‖ = ‖A‖ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose A
  rw [transpose_transpose, ht] at h
  exact h

/-- A square matrix whose entries are bounded by `c` has operator norm at most `N c`. -/
private lemma aux_norm_le_of_entry_le {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i j, |M i j| ≤ c) : ‖M‖ ≤ N * c := by
  have h1 : ‖M‖ * ‖M‖ ≤ trace (M * Mᵀ) := by
    have := opNorm_pow_le_trace M (k := 1) le_rfl
    rwa [pow_one, pow_one, aux_mul_transpose_self] at this
  have h2 : trace (M * Mᵀ) = ∑ i, ∑ j, M i j ^ 2 := by
    simp [trace, mul_apply, sq]
  have h3 : ∑ i : Fin N, ∑ j : Fin N, M i j ^ 2 ≤ ∑ _i : Fin N, ∑ _j : Fin N, c ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
  have h4 : ∑ _i : Fin N, ∑ _j : Fin N, c ^ 2 = ((N : ℝ) * c) ^ 2 := by
    simp [mul_pow]
    ring
  have h5 : ‖M‖ ^ 2 ≤ ((N : ℝ) * c) ^ 2 := by
    rw [sq]
    calc ‖M‖ * ‖M‖ ≤ trace (M * Mᵀ) := h1
      _ ≤ _ := by rw [h2]; exact h3.trans h4.le
  exact le_of_sq_le_sq h5 (by positivity)

/-- The norm of `W = U + Uᵀ + diag W` for symmetric `W` with entries bounded by `t`, where `U`
is the strictly upper part of `W`. -/
private lemma aux_norm_le_upper {N : ℕ} (W U : Matrix (Fin N) (Fin N) ℝ) (hsymm : Wᵀ = W)
    {t : ℝ} (ht : 0 ≤ t) (hbd : ∀ i j, |W i j| ≤ t)
    (hU : ∀ i j, U i j = if i < j then W i j else 0) : ‖W‖ ≤ 2 * ‖U‖ + t := by
  have hdec : W = U + Uᵀ + diagonal (fun i => W i i) := by
    ext i j
    simp only [Matrix.add_apply, transpose_apply, hU, diagonal_apply]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · have hW : W j i = W i j := by
        have := congrFun (congrFun hsymm i) j
        simpa [transpose_apply] using this
      simp [h, h.ne', not_lt.2 h.le, hW]
  have hUt : ‖Uᵀ‖ = ‖U‖ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using l2_opNorm_conjTranspose U
  have hdiag : ‖(diagonal (fun i => W i i) : Matrix (Fin N) (Fin N) ℝ)‖ ≤ t := by
    rw [l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg ht).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact hbd i i
  calc ‖W‖ = ‖U + Uᵀ + diagonal (fun i => W i i)‖ := by rw [← hdec]
    _ ≤ ‖U + Uᵀ‖ + ‖(diagonal (fun i => W i i) : Matrix (Fin N) (Fin N) ℝ)‖ := norm_add_le _ _
    _ ≤ (‖U‖ + ‖Uᵀ‖) + t := add_le_add (norm_add_le _ _) hdiag
    _ = 2 * ‖U‖ + t := by rw [hUt]; ring

/-! ## Independence with constant coordinates -/

/-- Extending an independent family by coordinates that vanish identically keeps independence. -/
private lemma aux_iIndepFun_extend {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {ι κ : Type*} [Finite ι]
    (Z : κ → Ω → ℝ) (e : ι → κ) (he : Function.Injective e)
    (hV : iIndepFun (fun i => Z (e i)) ℙ) (hZ : ∀ p, p ∉ Set.range e → ∀ ω, Z p ω = 0) :
    iIndepFun Z ℙ := by
  have := Fintype.ofFinite ι
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  by_cases hA : ∃ p ∈ S, p ∉ Set.range e ∧ (0 : ℝ) ∉ sets p
  · obtain ⟨p, hpS, hpe, hp0⟩ := hA
    have hempty : Z p ⁻¹' sets p = ∅ := by
      ext ω
      simp [hZ p hpe ω, hp0]
    have h1 : ℙ (⋂ i ∈ S, Z i ⁻¹' sets i) = 0 := by
      refine measure_mono_null ?_ (measure_empty (μ := (ℙ : Measure Ω)))
      intro ω hω
      have := Set.mem_iInter₂.1 hω p hpS
      rw [hempty] at this
      exact this
    rw [h1]
    exact (Finset.prod_eq_zero hpS (by rw [hempty]; exact measure_empty)).symm
  · push Not at hA
    set T : Finset ι := Finset.univ.filter (fun u => e u ∈ S) with hT
    have himg : S.filter (fun p => p ∈ Set.range e) = T.image e := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hT,
        Set.mem_range]
      constructor
      · rintro ⟨hp, u, rfl⟩
        exact ⟨u, hp, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, u, rfl⟩
    have hset : (⋂ i ∈ S, Z i ⁻¹' sets i) = ⋂ u ∈ T, (fun i => Z (e i)) u ⁻¹' sets (e u) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, hT, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro h u hu
        exact h (e u) hu
      · intro h p hp
        by_cases hpe : p ∈ Set.range e
        · obtain ⟨u, rfl⟩ := hpe
          exact h u hp
        · rw [hZ p hpe ω]
          exact hA p hp hpe
    have hone : ∀ p ∈ S.filter (fun p => p ∉ Set.range e), ℙ (Z p ⁻¹' sets p) = 1 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have : Z p ⁻¹' sets p = Set.univ := by
        ext ω
        simp [hZ p hp.2 ω, hA p hp.1 hp.2]
      rw [this]
      exact measure_univ
    have hprod : ∏ i ∈ S, ℙ (Z i ⁻¹' sets i) = ∏ u ∈ T, ℙ (Z (e u) ⁻¹' sets (e u)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ∈ Set.range e),
        Finset.prod_eq_one hone, mul_one, himg, Finset.prod_image]
      intro x _ y _ hxy
      exact he hxy
    rw [hset, hprod]
    exact hV.measure_inter_preimage_eq_mul T (fun u hu => hsets (e u) (by
      simpa only [hT, Finset.mem_filter, Finset.mem_univ, true_and] using hu))

/-! ## The choice of `k` -/

/-- `c (m + 1)^12 ≤ 2^m` for all large `m`. -/
private lemma aux_pow_two (c : ℝ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, c * ((m : ℝ) + 1) ^ 12 ≤ 2 ^ m := by
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

section Core

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- At fixed `N` and `k`: if `2 (2k)^6 b² ≤ 1` for `b = 2 N^{-1/4}` and the means of the
truncated entries of the strictly upper part are small (`N` times their bound is at most `1`),
the event `‖W‖ ≤ 12` fails with probability at most the sum of the truncation probability and
`2 N 2^{-k}`. -/
private lemma aux_core {C : ℕ → ℝ} {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (q : ℕ)
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W)
    (hsmall : 2 * ((2 * k : ℕ) : ℝ) ^ 6 * (2 * (N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1)
    (hM : (N : ℝ) * (max (C 4) 0 * (N : ℝ) ^ (-(5 / 4 : ℝ))) ≤ 1) :
    ℙ {ω | ‖W ω‖ ≤ 12}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4)) +
        ENNReal.ofReal (2 * N * (1 / 2) ^ k) := by
  classical
  set t : ℝ := (N : ℝ) ^ (-(1 / 4 : ℝ)) with ht
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
  have hh0sq : ∀ x, h0 x ^ 2 ≤ x ^ 2 := by
    intro x
    simp only [hh0]
    split_ifs
    · exact le_rfl
    · simpa using sq_nonneg x
  -- the strictly upper part of the truncated entries
  set g0 : Fin N × Fin N → ℝ → ℝ := fun p x => if p.1 < p.2 then h0 x else 0 with hg0
  have hg0m : ∀ p, Measurable (g0 p) := by
    intro p
    by_cases h : p.1 < p.2
    · simpa only [hg0, h, ↓reduceIte] using hh0m
    · simpa only [hg0, h, ↓reduceIte] using measurable_const
  have hg0bd : ∀ p x, |g0 p x| ≤ t := by
    intro p x
    simp only [hg0]
    split_ifs
    · exact hh0bd x
    · simp [htpos.le]
  have hg0sq : ∀ p x, g0 p x ^ 2 ≤ x ^ 2 := by
    intro p x
    simp only [hg0]
    split_ifs
    · exact hh0sq x
    · simpa using sq_nonneg x
  set U : Ω → Matrix (Fin N) (Fin N) ℝ := fun ω i j => g0 (i, j) (W ω i j) with hU
  have hUm : ∀ i j, Measurable fun ω => U ω i j := fun i j =>
    (hg0m (i, j)).comp (hW.measurable i j)
  have hUbd : ∀ ω i j, |U ω i j| ≤ t := fun ω i j => hg0bd _ _
  have hUint : ∀ i j, Integrable fun ω => U ω i j := fun i j =>
    Integrable.of_bound (hUm i j).aestronglyMeasurable t
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hUbd ω i j)
  have hU0 : ∀ i j, ¬ i < j → ∀ ω, U ω i j = 0 := by
    intro i j h ω
    simp [hU, hg0, h]
  set M : Matrix (Fin N) (Fin N) ℝ := fun i j => ∫ ω, U ω i j with hM_def
  have hM0 : ∀ i j, ¬ i < j → M i j = 0 := by
    intro i j h
    simp [hM_def, hU0 i j h]
  have hMt : ∀ i j, |M i j| ≤ t := by
    intro i j
    have := norm_integral_le_of_norm_le_const (μ := ℙ) (f := fun ω => U ω i j) (C := t)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hUbd ω i j)
    simpa using this
  have hMbd : ∀ i j, |M i j| ≤ max (C 4) 0 * (N : ℝ) ^ (-(5 / 4 : ℝ)) := by
    intro i j
    by_cases h : i < j
    · have hmean := wig_trunc_mean hN hW i j
      have hMeq : M i j = ∫ ω, (if |W ω i j| ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) then W ω i j else 0) := by
        simp [hM_def, hU, hg0, hh0, h, ht]
      rw [hMeq]
      exact hmean.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hNpos.le _))
    · rw [hM0 i j h, abs_zero]
      positivity
  have hMnorm : ‖M‖ ≤ 1 :=
    (aux_norm_le_of_entry_le M (by positivity) hMbd).trans hM
  -- the centred matrix
  set Y : Ω → Matrix (Fin N) (Fin N) ℝ := fun ω i j => U ω i j - M i j with hY
  have hY_eq : ∀ ω i j, Y ω i j = U ω i j - M i j := fun _ _ _ => rfl
  have hYm : ∀ i j, Measurable fun ω => Y ω i j := fun i j => (hUm i j).sub_const _
  have hYind : iIndepFun (fun (p : Fin N × Fin N) ω => Y ω p.1 p.2) ℙ := by
    refine aux_iIndepFun_extend (fun (p : Fin N × Fin N) ω => Y ω p.1 p.2)
      (fun u : UpperIdx N => u.1) Subtype.val_injective ?_ ?_
    · exact hW.indep.comp (fun u : UpperIdx N => fun x => g0 u.1 x - M u.1.1 u.1.2)
        (fun u => (hg0m u.1).sub_const _)
    · intro p hp ω
      have hp' : ¬ p.1 < p.2 := fun h => hp ⟨⟨p, h.le⟩, rfl⟩
      simp only [hY_eq, hU0 p.1 p.2 hp' ω, hM0 p.1 p.2 hp', sub_zero]
  have hYmean : ∀ i j, ∫ ω, Y ω i j = 0 := by
    intro i j
    simp only [hY_eq]
    rw [integral_sub (hUint i j) (integrable_const _)]
    simp [hM_def]
  have hX2int : ∀ i j, Integrable fun ω => W ω i j ^ 2 := by
    intro i j
    have h := (hW.integrable_moment 2 i j).const_mul ((N : ℝ)⁻¹)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [sq_abs, mul_pow, Real.sq_sqrt hNpos.le]
    field_simp
  have hU2le : ∀ i j, ∫ ω, U ω i j ^ 2 ≤ 1 / (N : ℝ) := by
    intro i j
    by_cases h : i < j
    · calc ∫ ω, U ω i j ^ 2 ≤ ∫ ω, W ω i j ^ 2 :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
              (hX2int i j) (Filter.Eventually.of_forall fun ω => hg0sq _ _)
        _ = 1 / (N : ℝ) := hW.var_off i j h.ne
    · simp only [hU0 i j h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        integral_zero]
      positivity
  have hYvar : ∀ i j, ∫ ω, Y ω i j ^ 2 ≤ 1 / (N : ℝ) := by
    intro i j
    have hexp : (fun ω => Y ω i j ^ 2) =
        fun ω => (U ω i j ^ 2 - 2 * M i j * U ω i j) + M i j ^ 2 := by
      funext ω
      rw [hY_eq]
      ring
    have hU2int : Integrable fun ω => U ω i j ^ 2 :=
      Integrable.of_bound ((hUm i j).pow_const 2).aestronglyMeasurable (t ^ 2)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hUbd ω i j) 2)
    rw [hexp, integral_add (f := fun ω => U ω i j ^ 2 - 2 * M i j * U ω i j)
      (g := fun _ => M i j ^ 2) (hU2int.sub ((hUint i j).const_mul _)) (integrable_const _),
      integral_sub (f := fun ω => U ω i j ^ 2) (g := fun ω => 2 * M i j * U ω i j) hU2int
        ((hUint i j).const_mul _), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    have : ∫ ω, U ω i j = M i j := rfl
    rw [this]
    nlinarith [sq_nonneg (M i j), hU2le i j]
  set b : ℝ := 2 * t with hb
  have hYbd : ∀ ω i j, |Y ω i j| ≤ b := by
    intro ω i j
    rw [hY_eq]
    calc |U ω i j - M i j| ≤ |U ω i j| + |M i j| := abs_sub _ _
      _ ≤ t + t := add_le_add (hUbd ω i j) (hMt i j)
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
  have hE := integral_trace_pow_le (τ := 1) (b := b) one_pos le_rfl hk
    (by simp) Y hYm hYind hYmean hYvar hYbd hbN hsmall
  -- integrability of the trace, through the walk expansion
  set f : Ω → ℝ := fun ω => trace ((Y ω * (Y ω)ᵀ) ^ k) with hf
  have hfint : Integrable f := by
    have hpt : f = fun ω => ∑ i : Fin k → Fin N, ∑ μ : Fin k → Fin N,
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
  -- Markov's inequality at level `18 ^ k`
  have hMk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (pow_nonneg (norm_nonneg _) k).trans (hfge ω)) hfint
    ((18 : ℝ) ^ k)
  have hLk : 2 * (1 : ℝ)⁻¹ * (9 / 1) ^ k * N = (18 : ℝ) ^ k * (2 * N * (1 / 2) ^ k) := by
    have h18 : (18 : ℝ) ^ k * (1 / 2) ^ k = 9 ^ k := by rw [← mul_pow]; norm_num
    calc 2 * (1 : ℝ)⁻¹ * (9 / 1) ^ k * N = 2 * N * 9 ^ k := by simp; ring
      _ = 2 * N * ((18 : ℝ) ^ k * (1 / 2) ^ k) := by rw [h18]
      _ = (18 : ℝ) ^ k * (2 * N * (1 / 2) ^ k) := by ring
  have hPreal : (ℙ : Measure Ω).real {ω | (18 : ℝ) ^ k ≤ f ω} ≤ 2 * N * (1 / 2) ^ k := by
    have h := hMk.trans (hE.trans_eq hLk)
    exact le_of_mul_le_mul_left h (pow_pos (by norm_num) k)
  have hP : ℙ {ω | (18 : ℝ) ^ k ≤ f ω} ≤ ENNReal.ofReal (2 * N * (1 / 2) ^ k) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hPreal
  -- the deterministic inclusion
  have hsub : {ω | ‖W ω‖ ≤ 12}ᶜ ⊆
      {ω | ∃ i j, (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ∪ {ω | (18 : ℝ) ^ k ≤ f ω} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt, not_le] at hcon
    obtain ⟨hbd, hlt⟩ := hcon
    apply hω
    have hUeq : ∀ i j, U ω i j = if i < j then W ω i j else 0 := by
      intro i j
      by_cases h : i < j
      · have h1 : |W ω i j| ≤ t := hbd i j
        simp [hU, hg0, hh0, h, h1]
      · simp [hU0 i j h ω, h]
    have hdec : U ω = Y ω + M := by
      ext i j
      rw [Matrix.add_apply, hY_eq]
      ring
    have hYY : ‖Y ω * (Y ω)ᵀ‖ < 18 := by
      by_contra h
      exact absurd ((pow_le_pow_left₀ (by norm_num) (not_lt.1 h) k).trans (hfge ω))
        (not_le.2 hlt)
    rw [aux_mul_transpose_self] at hYY
    have hYn : ‖Y ω‖ ≤ 17 / 4 := by
      by_contra h
      have h' : 17 / 4 < ‖Y ω‖ := not_le.1 h
      nlinarith
    have hUn : ‖U ω‖ ≤ 17 / 4 + 1 := by
      rw [hdec]
      linarith [norm_add_le (Y ω) M]
    have := aux_norm_le_upper (W ω) (U ω) (hW.symm ω) htpos.le hbd hUeq
    change ‖W ω‖ ≤ 12
    linarith
  calc ℙ {ω | ‖W ω‖ ≤ 12}ᶜ
      ≤ ℙ ({ω | ∃ i j, (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ∪ {ω | (18 : ℝ) ^ k ≤ f ω}) :=
        measure_mono hsub
    _ ≤ ℙ {ω | ∃ i j, (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} + ℙ {ω | (18 : ℝ) ^ k ≤ f ω} :=
        measure_union_le _ _
    _ ≤ _ := add_le_add (wig_trunc_prob hN hW q) hP

end Core

/-! ## The norm bound -/

/-- `‖W‖ ≤ C₀` with high probability, uniformly over the class of entry laws (the analogue for
Wigner matrices of Lemma 4.8), at fixed `N`. -/
theorem wig_norm_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (C : ℕ → ℝ) (D : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W →
      HighProbAt N D {ω | ‖W ω‖ ≤ C₀} := by
  refine ⟨12, by norm_num, fun C D => ?_⟩
  set D' : ℕ := ⌈D⌉₊ with hD'
  set q : ℕ := 4 * D' + 12 with hq
  set Cq : ℝ := max (C q) 0 with hCq
  set C4 : ℝ := max (C 4) 0 with hC4
  set a : ℕ := D' + 2 with ha
  obtain ⟨m₀, hm₀⟩ := aux_pow_two (64 * (2 * (a : ℝ)) ^ 12)
  refine ⟨max (max (2 ^ m₀) (⌈Cq + 2⌉₊ + 1)) (⌈C4 ^ 4⌉₊ + 1), fun N hN => ?_⟩
  intro Ω _ _ W hW
  have hN2 : 2 ^ m₀ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hN2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hCq0 : 0 ≤ Cq := le_max_right _ _
  have hC40 : 0 ≤ C4 := le_max_right _ _
  have hNbig : Cq + 2 ≤ N := by
    have h1 := Nat.le_ceil (Cq + 2)
    have h2 : ⌈Cq + 2⌉₊ + 1 ≤ N :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    have h3 : ((⌈Cq + 2⌉₊ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast h2
    linarith
  have hN4 : C4 ^ 4 ≤ N := by
    have h1 := Nat.le_ceil (C4 ^ 4)
    have h2 : ⌈C4 ^ 4⌉₊ + 1 ≤ N := le_of_max_le_right hN
    have h3 : ((⌈C4 ^ 4⌉₊ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast h2
    linarith
  have hDD' : D ≤ D' := Nat.le_ceil D
  set m := Nat.log 2 N with hm
  set k := a * (m + 1) with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hmm : m₀ ≤ m := Nat.le_log_of_pow_le one_lt_two hN2
  have h2m : 2 ^ m ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hNk : N ^ a < 2 ^ k := by
    rw [hk, mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self one_lt_two N) (by positivity)
  -- the condition `2 (2k)^6 b² ≤ 1` of the trace moment bound
  have hsmall : 2 * ((2 * k : ℕ) : ℝ) ^ 6 * (2 * (N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 := by
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
    have ht2 : ((N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 = (Real.sqrt N)⁻¹ := by
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
  have hM : (N : ℝ) * (max (C 4) 0 * (N : ℝ) ^ (-(5 / 4 : ℝ))) ≤ 1 := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-(5 / 4 : ℝ)) = (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
      conv_lhs => lhs; rw [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNpos]
      norm_num
    have h4 : C4 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have := Real.rpow_le_rpow (pow_nonneg hC40 4) hN4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hC40, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num,
        Real.rpow_one] at this
    have hpos4 : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hNpos _
    calc (N : ℝ) * (max (C 4) 0 * (N : ℝ) ^ (-(5 / 4 : ℝ)))
        = C4 * ((N : ℝ) * (N : ℝ) ^ (-(5 / 4 : ℝ))) := by rw [hC4]; ring
      _ = C4 / (N : ℝ) ^ (1 / 4 : ℝ) := by
          rw [h1, Real.rpow_neg hNpos.le]
          exact (div_eq_mul_inv _ _).symm
      _ ≤ 1 := by rw [div_le_one hpos4]; exact h4
  have hcore := aux_core hN1 hk1 q hW hsmall hM
  -- the two error terms
  set P : ℝ := (N : ℝ) ^ (-(D' : ℝ)) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNpos.le _
  have hy1 : (N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4) ≤ Cq * (P / N) := by
    have hz : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(q : ℝ) / 4) ≤ P / N := by
      rw [hP, ← Real.rpow_sub_one hNpos.ne',
        show (N : ℝ) ^ 2 * (N : ℝ) ^ (-(q : ℝ) / 4) = (N : ℝ) ^ ((2 : ℝ) + -(q : ℝ) / 4) by
          rw [Real.rpow_add hNpos, Real.rpow_two]]
      apply Real.rpow_le_rpow_of_exponent_le hN1r
      rw [hq]
      push_cast
      linarith
    have hw0 : 0 ≤ (N : ℝ) ^ (-(q : ℝ) / 4) := Real.rpow_nonneg hNpos.le _
    have hCCq : C q ≤ Cq := le_max_left _ _
    calc (N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4)
        ≤ (N : ℝ) ^ 2 * Cq * (N : ℝ) ^ (-(q : ℝ) / 4) := by gcongr
      _ = Cq * ((N : ℝ) ^ 2 * (N : ℝ) ^ (-(q : ℝ) / 4)) := by ring
      _ ≤ Cq * (P / N) := by gcongr
  have hy2 : 2 * (N : ℝ) * (1 / 2 : ℝ) ^ k ≤ 2 * (P / N) := by
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
    calc 2 * (N : ℝ) * (1 / 2 : ℝ) ^ k ≤ 2 * (N : ℝ) * ((N : ℝ) ^ a)⁻¹ := by gcongr
      _ = 2 * ((N : ℝ) * ((N : ℝ) ^ a)⁻¹) := by ring
      _ ≤ 2 * (P / N) := by gcongr
  have hPD : P ≤ (N : ℝ) ^ (-D) := by
    rw [hP]
    apply Real.rpow_le_rpow_of_exponent_le hN1r
    linarith
  unfold HighProbAt
  refine hcore.trans ?_
  calc ENNReal.ofReal ((N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4)) +
        ENNReal.ofReal (2 * N * (1 / 2) ^ k)
      ≤ ENNReal.ofReal (Cq * (P / N)) + ENNReal.ofReal (2 * (P / N)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hy1) (ENNReal.ofReal_le_ofReal hy2)
    _ = ENNReal.ofReal ((Cq + 2) * (P / N)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal P := by
        apply ENNReal.ofReal_le_ofReal
        calc (Cq + 2) * (P / N) ≤ N * (P / N) := by gcongr
          _ = P := by field_simp
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hPD

/-! ## Instances -/

/-- The norm bound for the Rademacher Wigner matrix. -/
example : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    HighProbAt N D {ω | ‖wigRad N ω‖ ≤ C₀} := by
  obtain ⟨C₀, hC₀, h⟩ := wig_norm_le
  refine ⟨C₀, hC₀, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h (fun _ => 1) D
  exact ⟨max N₀ 1, fun N hN => hN₀ N (le_of_max_le_left hN) (wigRad N)
    (wignerEntries_wigRad (le_of_max_le_right hN)).toClass⟩

/-- The norm bound for the GOE. -/
example : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    HighProbAt N D {ω | ‖goeW N ω‖ ≤ C₀} := by
  obtain ⟨C₀, hC₀, h⟩ := wig_norm_le
  refine ⟨C₀, hC₀, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h (fun p => (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p) D
  exact ⟨max N₀ 1, fun N hN => hN₀ N (le_of_max_le_left hN) (goeW N)
    ((isGOE_goeW N).classEntries (le_of_max_le_right hN))⟩

#print axioms wig_norm_le

end Anisotropic
