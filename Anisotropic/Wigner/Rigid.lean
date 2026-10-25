import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.AvgOutsideW
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.EdgeSupport
import Anisotropic.Wigner.Exclusion
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.Norm

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Theorem 12.4: rigidity of the extreme eigenvalues of `W + A` (class, model and literal forms) -/

/-- Theorem 12.4 (`thm:wigner_rig`) for the class of entry laws, at fixed `N`: there is
`τ ∈ (0, τ₀]` such that the entrywise and averaged laws for `(W^Gauss, D, 𝐃^W(τ, N))`, the
standing bound on `𝐃^W(τ, N)` and the rigid extremes of `W^Gauss + D` give rigid extremes of
`W + A`. -/
theorem wigner_rig_class (τA : ℝ) (C : ℕ → ℝ) (τ₀ ε D : ℝ) (hτA : 0 < τA) (hτ₀ : 0 < τ₀)
    (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τA⁻¹ → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      RigidExtremesWAt N ε D (specOf A) (fun ω => W ω + A) := by
  obtain ⟨C₀, hC₀, hnorm⟩ := wig_norm_le
  have hτAinv : 0 < τA⁻¹ := inv_pos.mpr hτA
  have hK : 0 < C₀ + 2 * τA⁻¹ := by positivity
  set τS : ℝ := min (min ε (1 / 24)) (C₀ + 2 * τA⁻¹)⁻¹ with hτS_def
  have hτS : 0 < τS := lt_min (lt_min hε (by norm_num)) (inv_pos.mpr hK)
  have hτS24 : τS ≤ 1 / 24 := (min_le_left _ _).trans (min_le_right _ _)
  have hτSε : τS ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hτSinv : C₀ + 2 * τA⁻¹ ≤ τS⁻¹ := by
    have h : τS ≤ (C₀ + 2 * τA⁻¹)⁻¹ := min_le_right _ _
    calc C₀ + 2 * τA⁻¹ = ((C₀ + 2 * τA⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ τS⁻¹ := inv_anti₀ hτS h
  set τ : ℝ := min τ₀ (τS / 4) with hτ_def
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hττS : τ ≤ τS / 4 := min_le_right _ _
  obtain ⟨ε₂, D₂, hε₂, N₂, hR⟩ :=
    rigid_of_outside τ τS C₀ (τS / 2) ε D hτ hττS (by linarith) hτSε hC₀.le (by positivity)
  obtain ⟨ε₁, D₁, hε₁, N₁, hP⟩ := wig_avg_outside τ τS C ε₂ D₂ hτ hττS hτS24 hε₂
  obtain ⟨N₃, hW⟩ := hnorm C D₂
  refine ⟨τ, hτ, min_le_left _ _, ε₁, D₁, hε₁, max (max N₁ N₂) N₃,
    fun N hN Ω _ _ A W hAh hAn hWc hsb he ha hr => ?_⟩
  have hN₁ : N₁ ≤ N := le_of_max_le_left (le_of_max_le_left hN)
  have hN₂ : N₂ ≤ N := le_of_max_le_right (le_of_max_le_left hN)
  have hN₃ : N₃ ≤ N := le_of_max_le_right hN
  have hA0 := norm_nonneg A
  have hAn' : ‖A‖ ≤ τS⁻¹ := by linarith
  have hC : C₀ + 2 * ‖A‖ ≤ τS⁻¹ := by linarith
  have hphi := hP N hN₁ A W hAh hAn' hWc hsb he ha hr
  rw [show -τS / 2 = -(τS / 2) by ring] at hphi
  exact hR N hN₂ A W hAh hC hWc.symm hsb (hW N hN₃ W hWc) hphi

/-- Theorem 12.4 (`thm:wigner_rig`) at fixed `N`, for the model of §12.1. -/
theorem wigner_rig (τA : ℝ) (C : ℕ → ℝ) (τ₀ ε D : ℝ) (hτA : 0 < τA) (hτ₀ : 0 < τ₀)
    (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      WignerModel τA C N A W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf A) (fun ω => goeW N ω + diagonal (specOf A)) →
      RigidExtremesWAt N ε D (specOf A) (fun ω => W ω + A) := by
  obtain ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, N₀, h⟩ := wigner_rig_class τA C τ₀ ε D hτA hτ₀ hε
  exact ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, N₀, fun N hN Ω _ _ A W hm =>
    h N hN A W hm.symmA hm.normA hm.entries.toClass⟩

/-- Theorem 12.4 as printed: under the interval-support condition `supp ϱ^W = [Lm, Lp]` of §12.1,
rigidity of the extremes of `W^Gauss + D` with respect to `[Lm, Lp]` gives that of `W + A`. -/
theorem wigner_rig_lit (τA : ℝ) (C : ℕ → ℝ) (τ₀ ε D : ℝ) (hτA : 0 < τA) (hτ₀ : 0 < τ₀)
    (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) (Lm Lp : ℝ),
      WignerModel τA C N A W → IntervalSupportW (specOf A) Lm Lp →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      RigidExtremesAt N ε₁ D₁ Lm Lp (fun ω => goeW N ω + diagonal (specOf A)) →
      RigidExtremesAt N ε D Lm Lp (fun ω => W ω + A) := by
  obtain ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, N₀, h⟩ := wigner_rig τA C τ₀ ε D hτA hτ₀ hε
  refine ⟨τ, hτ, hττ₀, ε₁, D₁, hε₁, max N₀ 1, fun N hN Ω _ _ A W Lm Lp hm hI => ?_⟩
  obtain ⟨hLm, hLp⟩ := intervalSupportW_eq (le_of_max_le_right hN) hI
  subst hLm hLp
  exact h N (le_of_max_le_left hN) A W hm

/-- Theorem 12.4 along `(wigRad N, aEx N)` with `τ₀ = 1/2`: the model and the standing bound are
discharged; the laws for `(W^Gauss, D)` and the rigid extremes of `W^Gauss + D` (the deformed GOE
local law and rigidity, not available at fixed `N`) stay as hypotheses. -/
example (ε D : ℝ) (hε : 0 < ε) : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf (aEx N))
        (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
      RigidExtremesWAt N ε D (specOf (aEx N)) (fun ω => wigRad N ω + aEx N) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, N₀, h⟩ :=
    wigner_rig (1 / 2) (fun _ => 1) (1 / 2) ε D (by norm_num) (by norm_num) hε
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, N₀, fun N hN hN1 => ?_⟩
  have hsb : StandingBoundW τ (specOf (aEx N)) (domW τ N) := by
    intro z hz i
    have ha : ∀ k, |specOf (aEx N) k| ≤ 1 / 4 := fun k =>
      (abs_specOf_le_norm (aEx_isHermitian N) k).trans (norm_aEx_le hN1)
    have h1 := standingBoundW_of_lt hN1 ha (by norm_num) z hz.1 i
    linarith
  exact h N hN (aEx N) (wigRad N) (wignerModel_rad hN1) hsb

/-- Theorem 12.4 for the class along `(wigRad N, aEx N)` with `τ_A = τ₀ = 1/2`: the symmetry and
norm of `A`, the entry class and the standing bound are discharged; the laws for `(W^Gauss, D)` and
the rigid extremes of `W^Gauss + D` stay as hypotheses. -/
example (ε D : ℝ) (hε : 0 < ε) : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
      RigidExtremesWAt N ε₁ D₁ (specOf (aEx N))
        (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
      RigidExtremesWAt N ε D (specOf (aEx N)) (fun ω => wigRad N ω + aEx N) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, N₀, h⟩ :=
    wigner_rig_class (1 / 2) (fun _ => 1) (1 / 2) ε D (by norm_num) (by norm_num) hε
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, N₀, fun N hN hN1 => ?_⟩
  have hsb : StandingBoundW τ (specOf (aEx N)) (domW τ N) := by
    intro z hz i
    have ha : ∀ k, |specOf (aEx N) k| ≤ 1 / 4 := fun k =>
      (abs_specOf_le_norm (aEx_isHermitian N) k).trans (norm_aEx_le hN1)
    have h1 := standingBoundW_of_lt hN1 ha (by norm_num) z hz.1 i
    linarith
  exact h N hN (aEx N) (wigRad N) (aEx_isHermitian N) ((norm_aEx_le hN1).trans (by norm_num))
    (wignerModel_rad hN1).entries.toClass hsb

/-- The literal form of Theorem 12.4 along `(wigRad N, aEx N)` with `τ₀ = 1/2`: the model and the
standing bound are discharged; the interval-support condition, the laws for `(W^Gauss, D)` and the
rigid extremes of `W^Gauss + D` with respect to `[Lm, Lp]` stay as hypotheses (conditional). -/
example (ε D : ℝ) (hε : 0 < ε) : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧ ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Lm Lp : ℝ, IntervalSupportW (specOf (aEx N)) Lm Lp →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW τ N) →
      RigidExtremesAt N ε₁ D₁ Lm Lp (fun ω => goeW N ω + diagonal (specOf (aEx N))) →
      RigidExtremesAt N ε D Lm Lp (fun ω => wigRad N ω + aEx N) := by
  obtain ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, N₀, h⟩ :=
    wigner_rig_lit (1 / 2) (fun _ => 1) (1 / 2) ε D (by norm_num) (by norm_num) hε
  refine ⟨τ, hτ, hτ2, ε₁, D₁, hε₁, N₀, fun N hN hN1 Lm Lp hI => ?_⟩
  have hsb : StandingBoundW τ (specOf (aEx N)) (domW τ N) := by
    intro z hz i
    have ha : ∀ k, |specOf (aEx N) k| ≤ 1 / 4 := fun k =>
      (abs_specOf_le_norm (aEx_isHermitian N) k).trans (norm_aEx_le hN1)
    have h1 := standingBoundW_of_lt hN1 ha (by norm_num) z hz.1 i
    linarith
  exact h N hN (aEx N) (wigRad N) Lm Lp (wignerModel_rad hN1) hI hsb

#print axioms wigner_rig_class
#print axioms wigner_rig
#print axioms wigner_rig_lit

end Anisotropic
