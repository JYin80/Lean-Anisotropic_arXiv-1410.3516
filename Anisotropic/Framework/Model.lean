module

public import Anisotropic.MainDefs
public import Mathlib

@[expose] public section

/-!
# Framework: the model and sign spaces

The model of Section 2.1 under (T_diag): the entry conditions and the conditions on `Σ`
of Assumption 2.1, the extension `Σ̲` of (def_ul_Sigma), and the spectral domain of
(def_D). The finite sign space `ι → Bool` with the uniform measure, on which Rademacher
entries `±1` are defined.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal

noncomputable section

namespace Anisotropic

/-! ## The model (Section 2.1, Assumption 2.1, (T_diag)) -/

section Model

variable {Ω : Type*} [MeasureSpace Ω]

end Model

/-! ## Finite sign spaces and the eigenvalues of the identity -/

/-- The fair coin on `Bool`. -/
def coinMeasure : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coinMeasure := by
  constructor
  simp [coinMeasure]
  rw [← two_mul, ENNReal.mul_inv_cancel] <;> simp

lemma integral_coinMeasure (f : Bool → ℝ) :
    ∫ b, f b ∂coinMeasure = (f true + f false) / 2 := by
  rw [coinMeasure, integral_smul_measure, integral_add_measure .of_finite .of_finite,
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

/-- The sign space `ι → Bool` with the product of fair coins. -/
def SignSpace (ι : Type) : Type := ι → Bool

instance (ι : Type) : MeasurableSpace (SignSpace ι) := MeasurableSpace.pi

instance (ι : Type) [Fintype ι] : MeasureSpace (SignSpace ι) :=
  ⟨Measure.pi fun _ : ι => coinMeasure⟩

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (ℙ : Measure (SignSpace ι)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : ι => coinMeasure))

lemma measurable_eval_sign {ι : Type} [Fintype ι] (p : ι) (g : Bool → ℝ) :
    Measurable fun ω : SignSpace ι => g (ω p) :=
  (Measurable.of_discrete (f := g)).comp (measurable_pi_apply p)

lemma integral_eval_sign {ι : Type} [Fintype ι] (p : ι) (g : Bool → ℝ) :
    ∫ ω : SignSpace ι, g (ω p) = (g true + g false) / 2 := by
  have := integral_comp_eval (μ := fun _ : ι => coinMeasure) (i := p) (f := g)
    (Measurable.of_discrete (f := g)).aestronglyMeasurable
  rw [← integral_coinMeasure]
  exact this

/-- The sign `±1` of a Boolean. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

lemma abs_signVal (b : Bool) : |signVal b| = 1 := by
  cases b <;> simp [signVal]

lemma eigenvalues_one {M : ℕ} (i : Fin M) :
    (Matrix.PosDef.one : (1 : Matrix (Fin M) (Fin M) ℝ).PosDef).isHermitian.eigenvalues i
      = 1 := by
  rw [Matrix.IsHermitian.eigenvalues_eq, Matrix.one_mulVec, dotProduct_comm,
    ← EuclideanSpace.inner_eq_star_dotProduct]
  simp [(Matrix.PosDef.one :
    (1 : Matrix (Fin M) (Fin M) ℝ).PosDef).isHermitian.eigenvectorBasis.orthonormal.1 i]

end Anisotropic

#check @Anisotropic.IsModel
#print axioms Anisotropic.IsModel
#print axioms Anisotropic.ulSigma
#print axioms Anisotropic.specDomain
