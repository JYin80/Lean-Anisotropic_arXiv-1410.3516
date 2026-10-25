import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Truncation of the entries of the class: probability and mean

Truncation of the entries `W_ij` of a matrix of the class of entry laws at the level `N^{-1/4}`
(`N^{-1/2+δ}` with `δ = 1/4` in the scale of `X = √N W`): the probability that some entry
exceeds the level, by Markov's inequality for the moments `E|√N W_ij|^q ≤ C_q` and a union bound,
and the size of the mean of a truncated entry, which equals minus the mean of the discarded tail
since `E W_ij = 0`. -/

section Trunc

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

private lemma aux_natCast_pos {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < N := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

private lemma aux_sqrt_mul_thr {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N * (N : ℝ) ^ (-(1 / 4 : ℝ)) = (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hpos := aux_natCast_pos hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
  congr 1
  ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma aux_integrable_entry {C : ℕ → ℝ} {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (hN : 1 ≤ N) (i j : Fin N) :
    Integrable fun ω => W ω i j := by
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (aux_natCast_pos hN)
  have h1 : Integrable (fun ω => Real.sqrt N * W ω i j) := by
    have hm : Measurable fun ω => Real.sqrt N * W ω i j := (hW.measurable i j).const_mul _
    rw [← integrable_norm_iff hm.aestronglyMeasurable]
    simpa [Real.norm_eq_abs] using hW.integrable_moment 1 i j
  have := h1.const_mul (Real.sqrt N)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  field_simp

private lemma aux_tail_le {C : ℕ → ℝ} {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (hN : 1 ≤ N) (q : ℕ) (i j : Fin N) :
    ℙ {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ≤
      ENNReal.ofReal (C q * (N : ℝ) ^ (-(q : ℝ) / 4)) := by
  have hpos := aux_natCast_pos hN
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hpos
  set ε : ℝ := (N : ℝ) ^ ((q : ℝ) / 4) with hε
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hpos _
  have hsub : {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ⊆
      {ω | ε ≤ |Real.sqrt N * W ω i j| ^ q} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ |Real.sqrt N * W ω i j| := by
      rw [abs_mul, abs_of_pos hs, ← aux_sqrt_mul_thr hN]
      exact mul_le_mul_of_nonneg_left hω.le hs.le
    have e : ε = ((N : ℝ) ^ (1 / 4 : ℝ)) ^ q := by
      rw [hε, ← Real.rpow_mul_natCast hpos.le]
      congr 1
      ring
    rw [e]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) h1 q
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (ℙ : Measure Ω))
    (f := fun ω => |Real.sqrt N * W ω i j| ^ q)
    (Filter.Eventually.of_forall fun ω => by positivity) (hW.integrable_moment q i j) ε
  have hmom := hW.moment q i j
  have hreal : (ℙ : Measure Ω).real {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ≤
      C q * (N : ℝ) ^ (-(q : ℝ) / 4) := by
    have h1 : (ℙ : Measure Ω).real {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ≤
        (ℙ : Measure Ω).real {x | ε ≤ |Real.sqrt N * W x i j| ^ q} :=
      measureReal_mono hsub
    have h2 : ε * (ℙ : Measure Ω).real {x | ε ≤ |Real.sqrt N * W x i j| ^ q} ≤ C q :=
      hmark.trans hmom
    have h3 : (N : ℝ) ^ (-(q : ℝ) / 4) = ε⁻¹ := by
      rw [hε, ← Real.rpow_neg hpos.le]
      congr 1
      ring
    rw [h3]
    have : (ℙ : Measure Ω).real {x | ε ≤ |Real.sqrt N * W x i j| ^ q} ≤ C q * ε⁻¹ := by
      rw [le_mul_inv_iff₀ hεpos]
      linarith
    exact h1.trans this
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Truncation for the class: `P(maxᵢⱼ |W_ij| > N^{−1/4}) ≤ N² C_q N^{−q/4}`. -/
theorem wig_trunc_prob {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (q : ℕ) :
    ℙ {ω | ∃ i j, (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4)) := by
  have hpos := aux_natCast_pos hN
  have hsub : {ω | ∃ i j, (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|} ⊆
      ⋃ p : Fin N × Fin N, {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω p.1 p.2|} := by
    intro ω ⟨i, j, h⟩
    exact Set.mem_iUnion.2 ⟨(i, j), h⟩
  have hbound := fun p : Fin N × Fin N => aux_tail_le hW hN q p.1 p.2
  have hCq : 0 ≤ C q :=
    (integral_nonneg fun ω => by positivity).trans (hW.moment q ⟨0, hN⟩ ⟨0, hN⟩)
  calc ℙ {ω | ∃ i j, (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω i j|}
      ≤ ℙ (⋃ p : Fin N × Fin N, {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω p.1 p.2|}) :=
        measure_mono hsub
    _ ≤ ∑ p : Fin N × Fin N, ℙ {ω | (N : ℝ) ^ (-(1 / 4 : ℝ)) < |W ω p.1 p.2|} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin N × Fin N, ENNReal.ofReal (C q * (N : ℝ) ^ (-(q : ℝ) / 4)) :=
        Finset.sum_le_sum fun p _ => hbound p
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hb : 0 ≤ C q * (N : ℝ) ^ (-(q : ℝ) / 4) :=
          mul_nonneg hCq (Real.rpow_nonneg hpos.le _)
        have h : (N : ℝ) ^ 2 * C q * (N : ℝ) ^ (-(q : ℝ) / 4) =
            ((N * N : ℕ) : ℝ) * (C q * (N : ℝ) ^ (-(q : ℝ) / 4)) := by
          push_cast
          ring
        rw [h, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

private lemma aux_const_eq {N : ℕ} (hN : 1 ≤ N) :
    (((N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 3)⁻¹ * (Real.sqrt N ^ 4)⁻¹ = (N : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have hpos := aux_natCast_pos hN
  have e1 : ((N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 3 = (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hpos.le]
    congr 1
    push_cast
    ring
  have e2 : Real.sqrt N ^ 4 = (N : ℝ) ^ (2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hpos.le]
    congr 1
    push_cast
    ring
  rw [e1, e2, ← mul_inv, ← Real.rpow_add hpos, ← Real.rpow_neg hpos.le]
  congr 1
  ring

/-- Recentring for the class: `|E[W_ij 1(|W_ij| ≤ N^{−1/4})]| ≤ C₄ N^{−5/4}`. -/
theorem wig_trunc_mean {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (i j : Fin N) :
    |∫ ω, (if |W ω i j| ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) then W ω i j else 0)| ≤
      C 4 * (N : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have hpos := aux_natCast_pos hN
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hpos
  set t : ℝ := (N : ℝ) ^ (-(1 / 4 : ℝ)) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hpos _
  set c : ℝ := (t ^ 3)⁻¹ * (Real.sqrt N ^ 4)⁻¹ with hc
  have hcpos : 0 ≤ c := by positivity
  have hcN : c = (N : ℝ) ^ (-(5 / 4 : ℝ)) := aux_const_eq hN
  have hint := aux_integrable_entry hW hN i j
  have hmeas := hW.measurable i j
  set A : Set Ω := {ω | t < |W ω i j|} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hmeas.abs
  have htr : (fun ω => if |W ω i j| ≤ t then W ω i j else 0) =
      fun ω => W ω i j - A.indicator (fun ω => W ω i j) ω := by
    funext ω
    by_cases h : |W ω i j| ≤ t
    · have : ω ∉ A := by simp [hA, h]
      rw [Set.indicator_of_notMem this]
      simp [h]
    · have : ω ∈ A := by simpa [hA] using not_le.1 h
      rw [Set.indicator_of_mem this]
      simp [h]
  have hind : Integrable (A.indicator fun ω => W ω i j) := hint.indicator hAm
  have hmean : ∫ ω, (if |W ω i j| ≤ t then W ω i j else 0) =
      -∫ ω, A.indicator (fun ω => W ω i j) ω := by
    rw [htr, integral_sub hint hind, hW.mean i j, zero_sub]
  have hg : Integrable fun ω => c * |Real.sqrt N * W ω i j| ^ 4 :=
    (hW.integrable_moment 4 i j).const_mul c
  have hpt : ∀ ω, ‖A.indicator (fun ω => W ω i j) ω‖ ≤ c * |Real.sqrt N * W ω i j| ^ 4 := by
    intro ω
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs]
      have h1 : t < |W ω i j| := h
      have h2 : t ^ 3 ≤ |W ω i j| ^ 3 := pow_le_pow_left₀ htpos.le h1.le 3
      have htn : 0 < t ^ 3 := pow_pos htpos 3
      have h3 : |Real.sqrt N * W ω i j| ^ 4 =
          Real.sqrt N ^ 4 * (|W ω i j| ^ 3 * |W ω i j|) := by
        rw [abs_mul, abs_of_pos hs, mul_pow, pow_succ |W ω i j| 3]
      rw [h3, hc]
      have h4 : (0 : ℝ) < Real.sqrt N ^ 4 := pow_pos hs _
      calc |W ω i j| = (t ^ 3)⁻¹ * (Real.sqrt N ^ 4)⁻¹ *
            (Real.sqrt N ^ 4 * (t ^ 3 * |W ω i j|)) := by
            field_simp
        _ ≤ (t ^ 3)⁻¹ * (Real.sqrt N ^ 4)⁻¹ *
            (Real.sqrt N ^ 4 * (|W ω i j| ^ 3 * |W ω i j|)) := by
            gcongr
    · rw [Set.indicator_of_notMem h]
      simp only [norm_zero]
      positivity
  calc |∫ ω, (if |W ω i j| ≤ t then W ω i j else 0)|
      = ‖∫ ω, A.indicator (fun ω => W ω i j) ω‖ := by
        rw [hmean, abs_neg, Real.norm_eq_abs]
    _ ≤ ∫ ω, c * |Real.sqrt N * W ω i j| ^ 4 :=
        norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
    _ = c * ∫ ω, |Real.sqrt N * W ω i j| ^ 4 := integral_const_mul _ _
    _ ≤ c * C 4 := mul_le_mul_of_nonneg_left (hW.moment 4 i j) hcpos
    _ = C 4 * (N : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [hcN, mul_comm]

end Trunc

/-! ## Instances -/

/-- The tail bound for the Rademacher Wigner matrix at `N = 16`, where `wigRad` has entries
`±1/4` and the level is `1/2`. -/
example (q : ℕ) :
    ℙ {ω | ∃ i j, ((16 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) < |wigRad 16 ω i j|} ≤
      ENNReal.ofReal (((16 : ℕ) : ℝ) ^ 2 * 1 * ((16 : ℕ) : ℝ) ^ (-(q : ℝ) / 4)) :=
  wig_trunc_prob (C := fun _ => 1) (by norm_num) (wignerEntries_wigRad (by norm_num)).toClass q

/-- The recentring bound for the Rademacher Wigner matrix at `N = 16`. -/
example (i j : Fin 16) :
    |∫ ω, (if |wigRad 16 ω i j| ≤ ((16 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) then wigRad 16 ω i j else 0)| ≤
      1 * ((16 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) :=
  wig_trunc_mean (C := fun _ => 1) (by norm_num) (wignerEntries_wigRad (by norm_num)).toClass i j

end Anisotropic
