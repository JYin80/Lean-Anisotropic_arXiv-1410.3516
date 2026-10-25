import Mathlib

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

/-- The entry conditions of Assumption 2.1 for a random `K × N` matrix `X`:
measurability, independence of all entries, (cond on entries of X) and
(moments of X-1) for all `p`, the latter with the integrability of `|√N X_{iμ}|^p`. -/
structure EntryAssumption (C : ℕ → ℝ) {K N : ℕ} (X : Ω → Matrix (Fin K) (Fin N) ℝ) :
    Prop where
  measurable : ∀ i μ, Measurable fun ω => X ω i μ
  indep : iIndepFun (fun (p : Fin K × Fin N) (ω : Ω) => X ω p.1 p.2) ℙ
  mean : ∀ i μ, ∫ ω, X ω i μ = 0
  var : ∀ i μ, ∫ ω, X ω i μ ^ 2 = 1 / (N : ℝ)
  integrable_moment : ∀ (p : ℕ) i μ, Integrable fun ω => |Real.sqrt N * X ω i μ| ^ p
  moment : ∀ (p : ℕ) i μ, ∫ ω, |Real.sqrt N * X ω i μ| ^ p ≤ C p

/-- The conditions of Assumption 2.1 on `Σ` under (T_diag): `Σ > 0`, (bound_Sigma)
`σ₁ ≤ τ⁻¹` for every eigenvalue, and (Sigma_gap) `π([0,τ]) ≤ 1 - τ`, where
`π = M⁻¹ ∑ᵢ δ_{σᵢ}` (def_pi), so that `M π([0,τ])` is the number of eigenvalues
in `[0,τ]` counted with multiplicity. -/
structure SigmaAssumption (τ : ℝ) {M : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) : Prop where
  posDef : Sig.PosDef
  eigenvalues_le : ∀ i, posDef.isHermitian.eigenvalues i ≤ τ⁻¹
  gap : ({i | posDef.isHermitian.eigenvalues i ∈ Set.Icc 0 τ}.ncard : ℝ) ≤ (1 - τ) * M

/-- Assumption 2.1 under (T_diag): (phi_bounded) `τ ≤ M/N ≤ τ⁻¹`, the entry conditions
on `X`, and the conditions on `Σ`. -/
structure IsModel (τ : ℝ) (C : ℕ → ℝ) (M N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) : Prop where
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  entries : EntryAssumption C X
  sigma : SigmaAssumption τ Sig

end Model

/-- The extension `Σ̲ = diag(Σ, 1)` of (def_ul_Sigma), as a complex `𝓘 × 𝓘` matrix. -/
def ulSigma {M : ℕ} (N : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) :
    Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (Sig.map (algebraMap ℝ ℂ)) 0 0 1

/-- The spectral domain `𝐃(τ,N)` of (def_D). -/
def specDomain (τ : ℝ) (N : ℕ) : Set ℂ :=
  {z | 0 < z.im ∧ τ ≤ ‖z‖ ∧ |z.re| ≤ τ⁻¹ ∧ (N : ℝ) ^ (-1 + τ) ≤ z.im ∧ z.im ≤ τ⁻¹}

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
