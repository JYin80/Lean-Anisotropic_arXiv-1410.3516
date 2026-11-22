module

public import Anisotropic.MainDefs
public import Anisotropic.Framework.Model

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal

noncomputable section

namespace Anisotropic

/-! ## Stochastic domination at fixed `N` (Definition 3.4) -/

section Dom

variable {Ω : Type*} [MeasureSpace Ω]

end Dom

section Calculus

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Two copies of `N^{-D}` are at most `N^{-(D-1)}` once `N ≥ 2`. -/
private lemma two_ofReal_le {N : ℕ} {D : ℝ} (hN : 2 ≤ N) :
    ENNReal.ofReal ((N : ℝ) ^ (-D)) + ENNReal.ofReal ((N : ℝ) ^ (-D)) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(D - 1))) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have hp : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hpos.le _
  rw [← ENNReal.ofReal_add hp hp]
  apply ENNReal.ofReal_le_ofReal
  have : (N : ℝ) ^ (-(D - 1)) = (N : ℝ) ^ (-D) * N := by
    rw [show -(D - 1) = -D + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
  rw [this]
  nlinarith

/-- Sum: `ξ₁ ≺ ζ₁`, `ξ₂ ≺ ζ₂` give `ξ₁ + ξ₂ ≺ ζ₁ + ζ₂`, at the cost `D ↦ D - 1`. -/
theorem DomAt.add {N : ℕ} {ε D : ℝ} {ξ₁ ξ₂ ζ₁ ζ₂ : Ω → ℝ} (hN : 2 ≤ N)
    (h₁ : DomAt N ε D ξ₁ ζ₁) (h₂ : DomAt N ε D ξ₂ ζ₂) :
    DomAt N ε (D - 1) (ξ₁ + ξ₂) (ζ₁ + ζ₂) := by
  unfold DomAt at *
  have hsub : {ω | (N : ℝ) ^ ε * (ζ₁ + ζ₂) ω < (ξ₁ + ξ₂) ω} ⊆
      {ω | (N : ℝ) ^ ε * ζ₁ ω < ξ₁ ω} ∪ {ω | (N : ℝ) ^ ε * ζ₂ ω < ξ₂ ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at hω ⊢
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    nlinarith [hc.1, hc.2]
  calc ℙ {ω | (N : ℝ) ^ ε * (ζ₁ + ζ₂) ω < (ξ₁ + ξ₂) ω}
      ≤ ℙ ({ω | (N : ℝ) ^ ε * ζ₁ ω < ξ₁ ω} ∪ {ω | (N : ℝ) ^ ε * ζ₂ ω < ξ₂ ω}) :=
        measure_mono hsub
    _ ≤ ℙ {ω | (N : ℝ) ^ ε * ζ₁ ω < ξ₁ ω} + ℙ {ω | (N : ℝ) ^ ε * ζ₂ ω < ξ₂ ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) + ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
        add_le_add h₁ h₂
    _ ≤ _ := two_ofReal_le hN

/-- Monotonicity in `ξ`, `ζ`, `ε`, `D`. -/
theorem DomAt.mono {N : ℕ} {ε ε' D D' : ℝ} {ξ ξ' ζ ζ' : Ω → ℝ} (hN : 1 ≤ N)
    (hξ : ∀ ω, ξ ω ≤ ξ' ω) (hζ : ∀ ω, ζ' ω ≤ ζ ω) (hζ0 : ∀ ω, 0 ≤ ζ ω)
    (hε : ε ≤ ε') (hD : D' ≤ D) (h : DomAt N ε D ξ' ζ') :
    DomAt N ε' D' ξ ζ := by
  unfold DomAt at *
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have hNε : (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε' := Real.rpow_le_rpow_of_exponent_le hN' hε
  have hNε0 : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg hpos.le _
  have hsub : {ω | (N : ℝ) ^ ε' * ζ ω < ξ ω} ⊆ {ω | (N : ℝ) ^ ε * ζ' ω < ξ' ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : (N : ℝ) ^ ε * ζ' ω ≤ (N : ℝ) ^ ε * ζ ω :=
      mul_le_mul_of_nonneg_left (hζ ω) hNε0
    have h2 : (N : ℝ) ^ ε * ζ ω ≤ (N : ℝ) ^ ε' * ζ ω :=
      mul_le_mul_of_nonneg_right hNε (hζ0 ω)
    linarith [hξ ω]
  refine (measure_mono hsub).trans (h.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_le hN' (by linarith)

/-- A bound holding on a high-probability event `A` holds with `D ↦ D - 1`. -/
theorem DomAt.of_highProbAt {N : ℕ} {ε D : ℝ} {ξ ζ : Ω → ℝ} {A : Set Ω} (hN : 2 ≤ N)
    (hA : HighProbAt N D A)
    (h : ℙ (A ∩ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω}) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :
    DomAt N ε (D - 1) ξ ζ := by
  unfold DomAt
  have hsub : {ω | (N : ℝ) ^ ε * ζ ω < ξ ω} ⊆
      (A ∩ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω}) ∪ Aᶜ := by
    intro ω hω
    by_cases hωA : ω ∈ A
    · exact Or.inl ⟨hωA, hω⟩
    · exact Or.inr hωA
  calc ℙ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω}
      ≤ ℙ ((A ∩ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω}) ∪ Aᶜ) := measure_mono hsub
    _ ≤ ℙ (A ∩ {ω | (N : ℝ) ^ ε * ζ ω < ξ ω}) + ℙ Aᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) + ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
        add_le_add h hA
    _ ≤ _ := two_ofReal_le hN

end Calculus

end Anisotropic
