module

public import Anisotropic.Framework.Domination

@[expose] public section

/-! ## Unions over at most `N^C` indices

Fixed-`N` union-bound forms of the statements on stochastic domination (Definition 3.4) and
high-probability events (Definition 4.7). -/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal

noncomputable section

namespace Anisotropic

section Calculus

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Union bound: at most `N^C` events of probability `≤ N^{-(D+C)}` have a union of probability
`≤ N^{-D}`. -/
private lemma union_bound_pow {ι : Type*} (s : Finset ι) {N : ℕ} {D C : ℝ}
    (hN : 1 ≤ N) (hs : (s.card : ℝ) ≤ (N : ℝ) ^ C) (E : ι → Set Ω)
    (h : ∀ i ∈ s, ℙ (E i) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + C)))) :
    ℙ (⋃ i ∈ s, E i) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hp : 0 ≤ (N : ℝ) ^ (-(D + C)) := Real.rpow_nonneg hpos.le _
  calc ℙ (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, ℙ (E i) := measure_biUnion_finset_le s E
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal ((N : ℝ) ^ (-(D + C))) := Finset.sum_le_sum h
    _ = ENNReal.ofReal ((s.card : ℝ) * (N : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        calc (s.card : ℝ) * (N : ℝ) ^ (-(D + C))
            ≤ (N : ℝ) ^ C * (N : ℝ) ^ (-(D + C)) := mul_le_mul_of_nonneg_right hs hp
          _ = (N : ℝ) ^ (-D) := by
              rw [← Real.rpow_add hpos]
              congr 1
              ring

/-- Simultaneous bound over at most `N^C` indices, at the cost `D + C ↦ D`. -/
theorem DomAt.measure_exists_lt {ι : Type*} (s : Finset ι) {N : ℕ} {ε D C : ℝ}
    (hN : 1 ≤ N) (hs : (s.card : ℝ) ≤ (N : ℝ) ^ C) {ξ ζ : ι → Ω → ℝ}
    (h : ∀ i ∈ s, DomAt N ε (D + C) (ξ i) (ζ i)) :
    ℙ {ω | ∃ i ∈ s, (N : ℝ) ^ ε * ζ i ω < ξ i ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hset : {ω | ∃ i ∈ s, (N : ℝ) ^ ε * ζ i ω < ξ i ω} =
      ⋃ i ∈ s, {ω | (N : ℝ) ^ ε * ζ i ω < ξ i ω} := by
    ext ω
    simp
  rw [hset]
  exact union_bound_pow s hN hs _ h

/-- Intersection of at most `N^C` high-probability events. -/
theorem HighProbAt.biInter {ι : Type*} (s : Finset ι) {N : ℕ} {D C : ℝ}
    (hN : 1 ≤ N) (hs : (s.card : ℝ) ≤ (N : ℝ) ^ C) {A : ι → Set Ω}
    (h : ∀ i ∈ s, HighProbAt N (D + C) (A i)) :
    HighProbAt N D (⋂ i ∈ s, A i) := by
  unfold HighProbAt
  have hset : (⋂ i ∈ s, A i)ᶜ = ⋃ i ∈ s, (A i)ᶜ := by
    ext ω
    simp
  rw [hset]
  exact union_bound_pow s hN hs _ h

end Calculus

end Anisotropic
