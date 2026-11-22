module

public import Anisotropic.MainDefs
public import Anisotropic.Density.Basic
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.Density.GenProp
public import Anisotropic.Density.Stability.EdgeTools
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Gaussian.Spectral
public import Anisotropic.Instances.MarchenkoPastur
public import Anisotropic.Instances.Models
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The curvature `ϖ_k`, the rescaled extreme eigenvalues `q_{k,l}` and the Gaussian reference value `bRef` -/

/-- The number of eigenvalues beyond the edge `k` on its gap side: `d_{k̂-1}` (odd `k`) or
`N - d_{k̂}` (even `k`). -/
def edgeD (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  if k % 2 = 1 then cumCount N σ ((k + 1) / 2 - 1) else N - cumCount N σ ((k + 1) / 2)

/-- `q_{k,l}` under (T_diag), from the eigenvalues of `Q_N = Xᵀ Σ X`. -/
def qVec (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  qVecA N (specOf Sig) (QN Sig Xm) k l

/-- The rescaled eigenvalues `N^{2/3} ϖ⁻¹ (λ_{d+i} - a)_{i ≤ l}` of a symmetric matrix at an
upper edge `a` with `d` eigenvalues above it. -/
def edgeQ (N : ℕ) (a ϖ : ℝ) (d l : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Fin l → ℝ :=
  fun i => (N : ℝ) ^ (2 / 3 : ℝ) / ϖ * (sortedEig A (d + (i + 1)) - a)

/-- Lemma A.3: `ϖ_k³ = |f''(x_k)|/2`. -/
theorem edgeScale_cube (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) :
    edgeScale N σ k ^ 3 = |fR2 N σ (xCrit N σ k)| / 2 := by
  unfold edgeScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem edgec2_pos {τ : ℝ} (hτ : 0 < τ) : 0 < edgec2 τ := by
  unfold edgec2 edgeCx edgecx
  have := Real.sqrt_pos.2 hτ
  positivity

/-- Lemma A.3: `c₂/2 ≤ ϖ_k³ ≤ C₂/2` at a regular edge. -/
theorem edgeScale_bounds {τ : ℝ} {N : ℕ} {σ : Fin M → ℝ} {k : ℕ}
    (h : DensityAssumptions τ N σ) (hk : RegularEdge τ N σ k) :
    0 < edgeScale N σ k ∧ edgec2 τ / 2 ≤ edgeScale N σ k ^ 3 ∧
      edgeScale N σ k ^ 3 ≤ edgeC2 τ / 2 := by
  have h1 := edgec2_le_fR2_xCrit h hk
  have h2 := abs_fR2_xCrit_le h hk
  have hc := edgec2_pos h.pos
  have h3 : edgec2 τ ≤ |fR2 N σ (xCrit N σ k)| := by
    refine h1.trans (le_trans (le_abs_self _) ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold edgeScale
    exact Real.rpow_pos_of_pos (by linarith) _
  · rw [edgeScale_cube]; linarith
  · rw [edgeScale_cube]; linarith

/-- `ϖ₁` at the Marchenko–Pastur point lies in `[(c₂/2)^{1/3}, (C₂/2)^{1/3}]` with `c₂ > 0`. -/
example {n : ℕ} (hn : 0 < n) :
    0 < edgeScale (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 ∧
      edgec2 (1 / 5) / 2 ≤ edgeScale (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 ^ 3 ∧
      edgeScale (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 ^ 3 ≤ edgeC2 (1 / 5) / 2 := by
  have hda : DensityAssumptions (1 / 5) (2 * n) (fun _ : Fin n => (1 : ℝ)) := by
    have := (isModel_radXn hn).diagModel_specOf.densityAssumptions (by norm_num)
    rwa [specOf_one_eq] at this
  exact edgeScale_bounds hda (regularEdge_mp hn)

/-- `0 < c₂(τ)` at `τ = 1/5`. -/
example : 0 < edgec2 (1 / 5 : ℝ) := edgec2_pos (by norm_num)

/-- `ϖ_k³ = |f''(x_k)|/2` at the Marchenko–Pastur point. -/
example {n : ℕ} :
    edgeScale (2 * n) (fun _ : Fin n => (1 : ℝ)) 1 ^ 3 =
      |fR2 (2 * n) (fun _ : Fin n => (1 : ℝ)) (xCrit (2 * n) (fun _ : Fin n => (1 : ℝ)) 1)| / 2 :=
  edgeScale_cube _ _ _

end Anisotropic
