module

public import Anisotropic.Entrywise.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Measurability of `G`, `lawMat`, `m_N` in the matrix -/

/-- The matrix `linH Σ⁻¹ A z` is continuous in the real matrix `A`. -/
private theorem continuous_linH {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
  unfold linH cplx
  refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
  · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
  · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal

/-- Every entry of `G` is a measurable function of the matrix `X` (for every `Σ`, `z`). -/
theorem measurable_G_apply {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ)
    (s t : Fin M ⊕ Fin N) : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t := by
  have hc := continuous_linH (N := N) Sig z
  have hdet : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => (linH Sig⁻¹ A z).det :=
    (hc.matrix_det).measurable
  have hadj : Measurable fun A : Matrix (Fin M) (Fin N) ℝ => (linH Sig⁻¹ A z).adjugate s t :=
    (Matrix.measurable_iff.1 (hc.matrix_adjugate).measurable) s t
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z s t) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ * (linH Sig⁻¹ A z).adjugate s t := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ s t = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [h]
  exact hdet.inv.mul hadj

theorem measurable_lawMat_apply {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ)
    (s t : Fin M ⊕ Fin N) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ => lawMat Sig A z s t := by
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => lawMat Sig A z s t) =
      fun A => ∑ a, ∑ b, (ulSigma N Sig)⁻¹ s a *
        (G Sig A z a b - piMat Sig (mFun N (specOf Sig) z) a b) * (ulSigma N Sig)⁻¹ b t := by
    funext A
    simp only [lawMat, Matrix.mul_apply, Finset.sum_mul, Matrix.sub_apply]
    rw [Finset.sum_comm]
  rw [h]
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact (((measurable_G_apply Sig z a b).sub_const _).const_mul _).mul_const _

theorem measurable_mN {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ => mN Sig A z := by
  unfold mN
  exact (Finset.measurable_sum _ fun μ _ =>
    measurable_G_apply Sig z (Sum.inr μ) (Sum.inr μ)).const_mul _

/-- Instance `M = N = 2`, `Σ = 1`, `z = i`: the statement and the theorem applied. -/
example : Measurable fun A : Matrix (Fin 2) (Fin 2) ℝ => mN (M := 2) (N := 2) 1 A Complex.I :=
  measurable_mN (M := 2) (N := 2) 1 Complex.I

end Anisotropic
