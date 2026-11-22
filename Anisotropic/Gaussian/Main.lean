module

public import Anisotropic.Gaussian.Lemma62
public import Anisotropic.Gaussian.Ensemble
public import Anisotropic.Entrywise.Main
public import Anisotropic.Density.Stability.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Proposition 6.1 = Theorem 3.21 for Gaussian `X` -/

/-- Proposition 6.1 (i) (Theorem 3.21 (i) for Gaussian `X`). -/
theorem gauss_aniso (τ c ε D : ℝ) (C : ℕ → ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsGaussianEnsemble X → IsModel τ C M N Sig X → SpectralDomain τ N S →
      OneXmOn c N (specOf Sig) S →
      EntrywiseLawAt N (ε / 4) (lawD1 ε D) (diagonal (specOf Sig)) X S →
      AnisotropicLawAt N ε D Sig X S := by
  obtain ⟨N₀, hN₀⟩ := anisoLaw_diag_gauss τ ε D hτ hε
  exact ⟨N₀, fun N hN Ω _ _ M Sig X S hX hm hS _ h =>
    aniso_of_diag hm.sigma.posDef.isHermitian hX
      (hN₀ N hN M (specOf Sig) X S hX hm.diagModel_specOf.pos hm.ratio_ge hm.ratio_le hS.1 h)⟩

/-- Proposition 6.1 (i) on the concrete ensemble. -/
theorem gauss_aniso_gaussX (τ c ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
      IsModel τ gaussMoment M N Sig (gaussX M N) → SpectralDomain τ N S →
      OneXmOn c N (specOf Sig) S →
      EntrywiseLawAt N (ε / 4) (lawD1 ε D) (diagonal (specOf Sig)) (gaussX M N) S →
      AnisotropicLawAt N ε D Sig (gaussX M N) S := by
  obtain ⟨N₀, hN₀⟩ := gauss_aniso τ c ε D gaussMoment hτ hc hε
  exact ⟨N₀, fun N hN M Sig S hm hS hx h =>
    hN₀ N hN M Sig (gaussX M N) S (gaussX_isGaussianEnsemble M N) hm hS hx h⟩

/-- Proposition 6.1 (ii) on the concrete ensemble. -/
theorem gauss_averaged_gaussX {N : ℕ} {ε D : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hSig : Sig.IsHermitian) {S : Set ℂ}
    (h : AveragedLawAt N ε D (diagonal (specOf Sig)) (gaussX M N) S) :
    AveragedLawAt N ε D Sig (gaussX M N) S :=
  gauss_averaged hSig (gaussX_isGaussianEnsemble M N) h

/-- Proposition 6.1 (Theorem 3.21 for Gaussian `X`): under (1+xm) and stability on `S`, the
anisotropic and the averaged local laws hold with parameters `(X, Σ, S)`. -/
theorem gauss_gen_iso (τ c C₀ C₁ K₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ),
      IsGaussianEnsemble X → IsModel τ C M N Sig X → SpectralDomain τ N S →
      OneXmOn c N (specOf Sig) S → StableOn C₀ C₁ K₀ N (specOf Sig) S →
      AnisotropicLawAt N ε D Sig X S ∧ AveragedLawAt N ε D Sig X S := by
  obtain ⟨N₁, h₁⟩ := gauss_aniso τ c ε D C hτ hc hε
  obtain ⟨N₂, h₂⟩ := diag_gen τ c C₀ C₁ K₀ C (ε / 4) (lawD1 ε D) hτ hc (by positivity)
  obtain ⟨N₃, h₃⟩ := diag_gen τ c C₀ C₁ K₀ C ε D hτ hc hε
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M Sig X S hX hm hS hx hst => ?_⟩
  have hd := hm.diagModel_specOf
  refine ⟨h₁ N (le_of_max_le_left hN) M Sig X S hX hm hS hx
      (h₂ N (le_of_max_le_left (le_of_max_le_right hN)) M (specOf Sig) X S hd hS hx hst).1, ?_⟩
  exact gauss_averaged hm.sigma.posDef.isHermitian hX
    (h₃ N (le_of_max_le_right (le_of_max_le_right hN)) M (specOf Sig) X S hd hS hx hst).2


/-! ## Instantiations -/

/-- `gauss_gen_iso` on the concrete ensemble `gaussX M N` at `τ = 1/3`, `c = 1`,
`C₀ = C₁ = 4`, `K₀ = 1`, `C = gaussMoment`, `ε = D = 1`. The hypotheses `IsModel`,
`SpectralDomain`, `OneXmOn`, `StableOn` are binders (conditional example): the threshold `N₀`
is existential, and `IsModel` at fixed `M` is incompatible with `N ≥ N₀`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ),
    IsModel (1 / 3) gaussMoment M N Sig (gaussX M N) → SpectralDomain (1 / 3) N S →
    OneXmOn 1 N (specOf Sig) S → StableOn 4 4 1 N (specOf Sig) S →
    AnisotropicLawAt N 1 1 Sig (gaussX M N) S ∧ AveragedLawAt N 1 1 Sig (gaussX M N) S := by
  obtain ⟨N₀, h⟩ := gauss_gen_iso (1 / 3) 1 4 4 1 gaussMoment 1 1 (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨N₀, fun N hN M Sig S hm hS hx hst =>
    h N hN M Sig (gaussX M N) S (gaussX_isGaussianEnsemble M N) hm hS hx hst⟩

end Anisotropic

#print axioms Anisotropic.gauss_aniso
#print axioms Anisotropic.gauss_aniso_gaussX
#print axioms Anisotropic.gauss_averaged_gaussX
#print axioms Anisotropic.gauss_gen_iso
