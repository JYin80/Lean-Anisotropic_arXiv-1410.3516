module

public import Anisotropic.MainDefs
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.LinAlg.Spectral
public import Anisotropic.LinAlg.Blocks
public import Anisotropic.Framework.Domination

@[expose] public section

/-!
# `(1+xm)` on a set, `Π`, `Ψ`, `m_N`, the weighted entries and Definition 3.20

The lower bound (1+xm) on a set, the matrix `Π` of (def_Pi), the error parameter `Ψ` of
(def_Psi), the normalized trace `m_N` of (def_m_N), the weights `σ̲` of (def_ul_Sigma), and the
entrywise, isotropic and averaged laws of Definition 3.20 at fixed `N, ε, D`. For `Σ = diag(σ)`
the general forms agree with the diagonal forms.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-- (1+xm) on `S` with constant `c`. -/
def OneXmOn (c : ℝ) (N : ℕ) (σ : Fin M → ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ i, c ≤ ‖1 + (σ i : ℂ) * mFun N σ z‖

/-- (def_Pi) for `Σ = diag(σ)`: `Π = diag(m_1, …, m_M, m, …, m)`. -/
def PiDiag (N : ℕ) (σ : Fin M → ℝ) (z : ℂ) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  fromBlocks (diagonal fun i => -(σ i : ℂ) / (1 + σ i * mFun N σ z)) 0 0 (mFun N σ z • 1)

/-- Complexification of `diag(σ)` is the complex diagonal matrix. -/
private theorem cplx_diagonal (σ : Fin M → ℝ) :
    cplx (diagonal σ) = diagonal fun i => (σ i : ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [cplx, h]

/-- The inverse of a vector of nonzero complex numbers, as a ring element of `ι → ℂ`. -/
private theorem ringInverse_pi {ι : Type*} {v : ι → ℂ} (hv : ∀ i, v i ≠ 0) :
    Ring.inverse v = fun i => (v i)⁻¹ := by
  have hu : IsUnit v := Pi.isUnit_iff.2 fun i => isUnit_iff_ne_zero.2 (hv i)
  have h := Ring.mul_inverse_cancel v hu
  funext i
  exact eq_inv_of_mul_eq_one_right (congrFun h i)

theorem piMat_diagonal {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 ≤ σ i) {z : ℂ} (hz : 0 < z.im) :
    piMat (N := N) (diagonal σ) (mFun N (specOf (diagonal σ)) z) = PiDiag N σ z := by
  rw [mFun_specOf_diagonal]
  have hm := (mFun_spec N σ hσ hz).1
  have hne : ∀ i, (1 : ℂ) + mFun N σ z * (σ i : ℂ) ≠ 0 := by
    intro i h
    rcases (hσ i).eq_or_lt with h0 | h0
    · rw [← h0] at h
      simp at h
    · have := congrArg Complex.im h
      simp at this
      rcases this with h2 | h2
      · linarith
      · exact h0.ne' h2
  unfold piMat PiDiag
  have h1 : (1 : Matrix (Fin M) (Fin M) ℂ) + mFun N σ z • cplx (diagonal σ)
      = diagonal fun i => 1 + mFun N σ z * (σ i : ℂ) := by
    rw [cplx_diagonal]
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [h1, inv_diagonal, ringInverse_pi hne, cplx_diagonal, diagonal_mul_diagonal,
    diagonal_neg]
  congr 3
  funext i
  have := hne i
  field_simp

theorem mN_eq_trace_GN {N : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    mN Sig Xm z = (N : ℂ)⁻¹ * trace (GN Sig Xm z) := by
  unfold mN trace
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [(GeqG hSig Xm hz).1]
  simp [fromBlocks_apply₂₂]

theorem isProbabilityMeasure_empMeasure {K : ℕ} (σ : Fin K → ℝ) (hK : 0 < K) :
    IsProbabilityMeasure (empMeasure σ) := by
  constructor
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  simp only [empMeasure, Measure.smul_apply, Measure.finsetSum_apply, MeasurableSet.univ,
    Measure.dirac_apply', Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel hK0 (ENNReal.natCast_ne_top K)

/-- `m_N` is the Stieltjes transform of the empirical spectral measure of `XᵀΣX`. -/
theorem mN_eq_resolventTransform {N : ℕ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) :
    mN Sig Xm z = resolventTransform (empMeasure (specOf (Xmᵀ * Sig * Xm))) z := by
  have hA := XSX_isHermitian hSig.1 Xm
  have hnorm : ∀ k, ∑ μ, ((hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp μ) = 1 := by
    intro k
    have h1 := (hA.eigenvectorBasis.orthonormal.1 k)
    have h2 := EuclideanSpace.real_norm_sq_eq (hA.eigenvectorBasis k)
    rw [h1] at h2
    simpa [sq] using h2.symm
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := fun x h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hL : mN Sig Xm z = (N : ℂ)⁻¹ * ∑ k, (((hA.eigenvalues k : ℝ) : ℂ) - z)⁻¹ := by
    rw [mN_eq_trace_GN hSig Xm hz]
    congr 1
    unfold trace
    simp only [diag_apply, GN_spec hSig Xm hz]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have h1 : ∑ μ, (((hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis k).ofLp μ : ℝ) : ℂ)
        = 1 := by
      rw [← Complex.ofReal_sum, hnorm k, Complex.ofReal_one]
    rw [h1, one_mul]
  rw [hL, specOf_eq hA, resolventTransform_apply, empMeasure,
    integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
    rw [Complex.real_smul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp
  · intro k _
    exact integrable_dirac (by simp [resolvent, Ring.inverse_eq_inv'])

/-- `σ̲ = (σ, 1)`, the diagonal of `Σ̲` for `Σ = diag(σ)` ((def_ul_Sigma)). -/
def sigS {N : ℕ} (σ : Fin M → ℝ) : Fin M ⊕ Fin N → ℝ := Sum.elim σ fun _ => 1

/-- The weighted entry `A_{st} / (σ̲_s σ̲_t)`. -/
def wEnt {N : ℕ} (σ : Fin M → ℝ) (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ)
    (s t : Fin M ⊕ Fin N) : ℂ :=
  A s t / ((sigS σ s : ℂ) * sigS σ t)

theorem wEnt_eq {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    (A : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ) (s t : Fin M ⊕ Fin N) :
    wEnt σ A s t = ((ulSigma N (diagonal σ))⁻¹ * A * (ulSigma N (diagonal σ))⁻¹) s t := by
  have h : ulSigma N (diagonal σ)
      = diagonal fun s : Fin M ⊕ Fin N => (sigS (N := N) σ s : ℂ) := by
    have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) = diagonal fun _ => 1 := diagonal_one.symm
    change fromBlocks (cplx (diagonal σ)) 0 0 1 = _
    rw [cplx_diagonal, h1, fromBlocks_diagonal]
    congr 1
    funext s
    cases s <;> simp [sigS]
  have hne : ∀ s : Fin M ⊕ Fin N, (sigS (N := N) σ s : ℂ) ≠ 0 := by
    intro s
    cases s with
    | inl i => simpa [sigS] using (hσ i).ne'
    | inr μ => simp [sigS]
  rw [h, inv_diagonal, ringInverse_pi hne, Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold wEnt
  field_simp

section Laws

variable {Ω : Type*} [MeasureSpace Ω]

/-- Definition 3.20 (i) at fixed `N, ε, D`: (entrywise law) on `S`. -/
def EntrywiseLawAt (N : ℕ) (ε D : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ s t, ODomAt N ε D (fun ω => lawMat Sig (X ω) z s t)
    (fun _ => Psi N (specOf Sig) z)

/-- Definition 3.20 (i) for `Σ = diag(σ)`, entrywise in `σ`. -/
def EntrywiseLawDiagAt (N : ℕ) (ε D : ℝ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ s t, ODomAt N ε D (fun ω => wEnt σ (G (diagonal σ) (X ω) z - PiDiag N σ z) s t)
    (fun _ => Psi N σ z)

/-- Definition 3.20 (iii) for `Σ = diag(σ)`. -/
def AveragedLawDiagAt (N : ℕ) (ε D : ℝ) (σ : Fin M → ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ODomAt N ε D (fun ω => mN (diagonal σ) (X ω) z - mFun N σ z)
    (fun _ => 1 / (N * z.im))

theorem entrywiseLawAt_diagonal_iff {N : ℕ} {ε D : ℝ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ} (hS : ∀ z ∈ S, 0 < z.im) :
    EntrywiseLawAt N ε D (diagonal σ) X S ↔ EntrywiseLawDiagAt N ε D σ X S := by
  unfold EntrywiseLawAt EntrywiseLawDiagAt
  refine forall_congr' fun z => forall_congr' fun hz => forall_congr' fun s =>
    forall_congr' fun t => ?_
  have e1 : ∀ ω, lawMat (diagonal σ) (X ω) z s t
      = wEnt σ (G (diagonal σ) (X ω) z - PiDiag N σ z) s t := by
    intro ω
    unfold lawMat
    rw [← wEnt_eq hσ, piMat_diagonal (fun i => (hσ i).le) (hS z hz)]
  have e2 : Psi N (specOf (diagonal σ)) z = Psi N σ z := by
    unfold Psi
    rw [mFun_specOf_diagonal]
  simp only [e1, e2]

theorem averagedLawAt_diagonal_iff {N : ℕ} {ε D : ℝ} {σ : Fin M → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} {S : Set ℂ} :
    AveragedLawAt N ε D (diagonal σ) X S ↔ AveragedLawDiagAt N ε D σ X S := by
  unfold AveragedLawAt AveragedLawDiagAt
  simp only [mFun_specOf_diagonal]

end Laws

/-! ## Checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `z = 2i` -/

section Checks

example (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) (s t : Fin 2 ⊕ Fin 2) :
    wEnt (fun _ : Fin 2 => (1 : ℝ)) A s t
      = ((ulSigma 2 (diagonal fun _ : Fin 2 => (1 : ℝ)))⁻¹ * A
        * (ulSigma 2 (diagonal fun _ : Fin 2 => (1 : ℝ)))⁻¹) s t :=
  wEnt_eq (fun _ => one_pos) A s t

example : IsProbabilityMeasure (empMeasure fun _ : Fin 2 => (1 : ℝ)) :=
  isProbabilityMeasure_empMeasure _ (by norm_num)

end Checks

end Anisotropic

#print axioms Anisotropic.piMat_diagonal
#print axioms Anisotropic.mN_eq_trace_GN
#print axioms Anisotropic.isProbabilityMeasure_empMeasure
#print axioms Anisotropic.mN_eq_resolventTransform
#print axioms Anisotropic.wEnt_eq
#print axioms Anisotropic.entrywiseLawAt_diagonal_iff
#print axioms Anisotropic.averagedLawAt_diagonal_iff
