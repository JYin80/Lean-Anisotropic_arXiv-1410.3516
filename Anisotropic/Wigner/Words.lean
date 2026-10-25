import Anisotropic.Comparison.Words
import Anisotropic.Framework.Domination
import Anisotropic.LinAlg.Basic
import Anisotropic.Wigner.Defs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The resolvent expansion in a symmetric entry: updates, coefficients, words -/

/-- `W` with the entries `(i, j)` and `(j, i)` replaced by `t`. -/
def Wupd {N : ℕ} (Wm : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun s u => if (s = i ∧ u = j) ∨ (s = j ∧ u = i) then t else Wm s u

/-- The symmetric update direction `E_{ij} + E_{ji}` (`E_{ii}` when `i = j`). -/
def deltaW {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun s u => if (s = i ∧ u = j) ∨ (s = j ∧ u = i) then 1 else 0

/-- `a_k = (−1)^k (G (Δ G)^k − δ_{k0} Π)_{vv}`: the coefficient of `t^k` in `(G − Π)_{vv}` along
the entry `(i, j)` at the base matrix `Wm`. -/
def resCoeffW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ) (i j : Fin N)
    (k : ℕ) : ℂ :=
  (-1) ^ k * ent (GW A Wm z * (deltaW i j * GW A Wm z) ^ k - if k = 0 then piW A z else 0) v v

/-! ### Concrete checks at `N = 2` (Section 12.2, the variables `(W_{ij})_{i ≤ j}`)

An off-diagonal update sets both mirrored entries and keeps the diagonal; a diagonal update
changes one entry, and its direction has entry `1` there; the coefficient `a_0` is
`(G − Π)_{vv}` and `a_1` is `−(G Δ G)_{vv}`. -/

example : Wupd (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 5 0 1 = 5 ∧
    Wupd (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 5 1 0 = 5 ∧
    Wupd (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 5 0 0 = 0 ∧
    Wupd (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 5 0 0 = 5 ∧
    Wupd (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 5 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Wupd]

example : deltaW (0 : Fin 2) 1 = !![0, 1; 1, 0] ∧ deltaW (0 : Fin 2) 0 = !![1, 0; 0, 0] := by
  constructor <;> ext s u <;> fin_cases s <;> fin_cases u <;> simp [deltaW]

example (A Wm : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) (v : Fin 2 → ℝ) :
    resCoeffW A Wm z v 0 1 0 = ent (GW A Wm z - piW A z) v v ∧
    resCoeffW A Wm z v 0 1 1 = -ent (GW A Wm z * (deltaW 0 1 * GW A Wm z)) v v := by
  constructor <;> simp [resCoeffW]

#print axioms Wupd
#print axioms deltaW
#print axioms resCoeffW

end Anisotropic
