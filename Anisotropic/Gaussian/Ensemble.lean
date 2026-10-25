import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Framework.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # The concrete Gaussian ensemble: `GaussSpace`/`gaussX`, the model instance -/

/-- Assumption 2.1 for the concrete Gaussian ensemble, with `C = gaussMoment`. -/
theorem isModel_gaussX {τ : ℝ} {M N : ℕ} (hN : 1 ≤ N) {Sig : Matrix (Fin M) (Fin M) ℝ}
    (h₁ : τ ≤ (M : ℝ) / N) (h₂ : (M : ℝ) / N ≤ τ⁻¹) (hS : SigmaAssumption τ Sig) :
    IsModel τ gaussMoment M N Sig (gaussX M N) :=
  ⟨h₁, h₂, (gaussX_isGaussianEnsemble M N).entryAssumption hN, hS⟩

/-- A Gaussian ensemble is measurable as a matrix-valued map. -/
theorem IsGaussianEnsemble.measurable_mat {Ω : Type*} [MeasureSpace Ω] {K N : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : IsGaussianEnsemble X) : Measurable X :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hX.measurable i μ

section Law

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The joint law of the entries is the product of the laws `N(0, 1/N)`. -/
theorem IsGaussianEnsemble.map_entries {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) :
    (ℙ : Measure Ω).map (fun ω (p : Fin K × Fin N) => X ω p.1 p.2) =
      Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun (p : Fin K × Fin N) ω => X ω p.1 p.2)
    fun p => (hX.measurable p.1 p.2).aemeasurable).1 hX.indep
  rw [h]
  congr 1
  funext p
  exact hX.law p.1 p.2

end Law

example : IsProbabilityMeasure (ℙ : Measure (GaussSpace 2 2)) := inferInstance

/-- `M = N = 2`, `Σ = I`, `τ = 1/3`: the Gaussian ensemble satisfies Assumption 2.1. -/
example : IsModel (1 / 3 : ℝ) gaussMoment 2 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) (gaussX 2 2) :=
  isModel_gaussX (by norm_num) (by norm_num) (by norm_num)
    { posDef := Matrix.PosDef.one
      eigenvalues_le := fun i => by
        rw [eigenvalues_one]
        norm_num
      gap := by
        have h : {i : Fin 2 | (Matrix.PosDef.one :
            (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef).isHermitian.eigenvalues i
              ∈ Set.Icc 0 (1 / 3 : ℝ)} = ∅ := by
          ext i
          simp only [eigenvalues_one, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
          norm_num
        rw [h]
        norm_num }

/-- `measurable_mat` applied to the `2 × 2` Gaussian ensemble. -/
example : Measurable (gaussX 2 2) := (gaussX_isGaussianEnsemble 2 2).measurable_mat

/-- `map_entries` applied to the `2 × 2` Gaussian ensemble. -/
example : (ℙ : Measure (GaussSpace 2 2)).map
      (fun ω (p : Fin 2 × Fin 2) => gaussX 2 2 ω p.1 p.2) =
    Measure.pi fun _ : Fin 2 × Fin 2 => gaussianReal 0 ((2 : ℕ) : ℝ≥0)⁻¹ :=
  (gaussX_isGaussianEnsemble 2 2).map_entries

end Anisotropic

#print axioms Anisotropic.isModel_gaussX
#print axioms Anisotropic.IsGaussianEnsemble.measurable_mat
#print axioms Anisotropic.IsGaussianEnsemble.map_entries
