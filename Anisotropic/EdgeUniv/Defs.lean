import Anisotropic.Density.Basic
import Anisotropic.Density.Count
import Anisotropic.Density.Critical
import Anisotropic.Density.GenProp
import Anisotropic.Density.Stability.EdgeTools
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Gaussian.Spectral
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Instances.Models
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Rigidity.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The curvature `ϖ_k`, the rescaled extreme eigenvalues `q_{k,l}` and the Gaussian reference value `bRef` -/

/-- `ϖ_k = (|f''(x_k)|/2)^{1/3}`. -/
def edgeScale (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℝ :=
  (|fR2 N σ (xCrit N σ k)| / 2) ^ (1 / 3 : ℝ)

/-- The sign `(-1)^{k+1}`: `1` at the upper end of a component, `-1` at its lower end. -/
def edgeSign (k : ℕ) : ℝ := if k % 2 = 1 then 1 else -1

/-- The index (in decreasing order) of the `i`-th extreme eigenvalue at the edge `k`:
`d_{k̂-1} + i` for odd `k` and `d_{k̂} + 1 - i` for even `k`, `k̂ = ⌈k/2⌉`. -/
def edgeIdx (N : ℕ) (σ : Fin M → ℝ) (k i : ℕ) : ℕ :=
  if k % 2 = 1 then cumCount N σ ((k + 1) / 2 - 1) + i
  else cumCount N σ ((k + 1) / 2) + 1 - i

/-- The number of eigenvalues beyond the edge `k` on its gap side: `d_{k̂-1}` (odd `k`) or
`N - d_{k̂}` (even `k`). -/
def edgeD (N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : ℕ :=
  if k % 2 = 1 then cumCount N σ ((k + 1) / 2 - 1) else N - cumCount N σ ((k + 1) / 2)

/-- `q_{k,l}` for a symmetric `N × N` matrix `A` and the spectral data `σ`:
`q_{2j-1,l} = N^{2/3} ϖ⁻¹ (λ_{j,i} - a_{2j-1})_{i ≤ l}`,
`q_{2j,l} = -N^{2/3} ϖ⁻¹ (λ_{j,N_j+1-i} - a_{2j})_{i ≤ l}`. -/
def qVecA (N : ℕ) (σ : Fin M → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  fun i => edgeSign k * (N : ℝ) ^ (2 / 3 : ℝ) / edgeScale N σ k *
    (sortedEig A (edgeIdx N σ k (i + 1)) - edgeVal N σ k)

/-- `q_{k,l}` under (T_diag), from the eigenvalues of `Q_N = Xᵀ Σ X`. -/
def qVec (Sig : Matrix (Fin M) (Fin M) ℝ) (Xm : Matrix (Fin M) (Fin N) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  qVecA N (specOf Sig) (QN Sig Xm) k l

/-- `q_{k,l}` for a general `T`, from the eigenvalues of `Xᵀ Tᵀ T X` and the spectral data of
`Σ = T Tᵀ`. -/
def qVecT {K : ℕ} (T : Matrix (Fin M) (Fin K) ℝ) (Xm : Matrix (Fin K) (Fin N) ℝ) (k l : ℕ) :
    Fin l → ℝ :=
  qVecA N (specOf (T * Tᵀ)) (QN (Tᵀ * T) Xm) k l

/-- The reference value `b_N(h, π)` of Theorem 3.18: `E h(q_{k,l})` for Gaussian `X` and
`Σ = diag(σ)`. -/
def bRef (N : ℕ) (σ : Fin M → ℝ) (k l : ℕ) (h : (Fin l → ℝ) → ℝ) : ℝ :=
  ∫ ω, h (qVecA N σ (QN (diagonal σ) (gaussX M N ω)) k l)

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
