import Anisotropic.LinAlg.Expansion
import Anisotropic.LinAlg.Minor
import Anisotropic.LinAlg.Ward
import Anisotropic.Comparison.Notation
import Anisotropic.Comparison.Words

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Letters, factors, the minor `G^{(μ)}`, brackets (Definition 8.6), the split of `G` (G_split) -/

/-- The three letters of §8: `V` for `v̄`, `I` for `e_i`, `M` for `e_μ`. -/
inductive Letter
  | V
  | I
  | M
  deriving DecidableEq, Repr

instance : Fintype Letter := ⟨{.V, .I, .M}, by intro x; cases x <;> simp⟩

/-- The letter `[t]` of the first letter of a pair (`true` = `𝐢𝛍`). -/
def Letter.ofT (b : Bool) : Letter := if b then .I else .M

/-- The letter `[s]` of the second letter of a pair (`true` = `𝐢𝛍`). -/
def Letter.ofS (b : Bool) : Letter := if b then .M else .I

/-- The row letter of the `l`-th factor `G_{x_l y_l}` of a word with `k + 1` pairs:
`x_0 = V`, `x_l = s_{l+1}`. -/
def factorX {k : ℕ} (w : Word (k + 1)) (l : Fin (k + 2)) : Letter :=
  if h : (l : ℕ) = 0 then .V else Letter.ofS (w ⟨(l : ℕ) - 1, by omega⟩)

/-- The column letter of the `l`-th factor: `y_l = t_{l+1}`, `y_{k+1} = V`. -/
def factorY {k : ℕ} (w : Word (k + 1)) (l : Fin (k + 2)) : Letter :=
  if h : (l : ℕ) < k + 1 then Letter.ofT (w ⟨l, h⟩) else .V

/-- The vector of a letter: `V ↦ v̄`, `I ↦ e_i`, `M ↦ e_μ`. -/
def letVec (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) :
    Letter → (Fin M ⊕ Fin N → ℝ)
  | .V => vbar Sig v
  | .I => eI (Sum.inl i)
  | .M => eI (Sum.inr μ)

/-- `G^{(μ)}`: the minor with row and column `μ` removed, extended by zero. -/
noncomputable abbrev Gmu (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ :=
  G1 Sig A z (Sum.inr μ)

/-- The coefficients of `(G^{(μ)} X)_{xμ} = ∑_j G^{(μ)}_{x j} X_{jμ}`. -/
def colC (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (x : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (j : Fin M) : ℂ :=
  ent (Gmu Sig A z μ) x (eI (Sum.inl j))

/-- The coefficients of `(X^* G^{(μ)})_{μ y} = ∑_j X_{jμ} G^{(μ)}_{j y}`. -/
def rowC (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (y : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (j : Fin M) : ℂ :=
  ent (Gmu Sig A z μ) (eI (Sum.inl j)) y

/-- The linear form `∑_j c_j y_j` of a column `y`. -/
def linForm (c : Fin M → ℂ) (y : Fin M → ℝ) : ℂ := ∑ j, c j * (y j : ℂ)

/-- The degree of `[G_{xy}]^s` in the column `X_μ` (Definition 8.7 (iv)); `0` on zero brackets. -/
def degTab (x y : Letter) (s : Fin 3) : ℕ :=
  if s = 0 then 0
  else if s = 1 then (if x = .M then 0 else 1) + (if y = .M then 0 else 1)
  else if x = .V then (if y = .M then 0 else 1)
  else if y = .V then (if x = .M then 0 else 1) else 0

/-- The identically vanishing brackets: `[G_{VM}]^0`, `[G_{MV}]^0`, `[G_{IM}]^{0,2}`,
`[G_{MI}]^{0,2}`, `[G_{II}]^2`, `[G_{MM}]^{0,2}`. -/
def zeroTab (x y : Letter) (s : Fin 3) : Bool :=
  if s = 0 then (x == .M || y == .M) else if s = 1 then false else (x != .V && y != .V)

/-- The number of letters `M` among `x, y`. -/
def nMu (x y : Letter) : ℕ := (if x = .M then 1 else 0) + (if y = .M then 1 else 0)

/-- The scalar factor of `[G_{xy}]^s` (Definition 8.6): `G^{(μ)}_{xy}` for `s = 0`, a sign
otherwise. -/
def brackScal (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) : ℂ :=
  if s = 0 then ent (Gmu Sig A z μ) (letVec Sig v i μ x) (letVec Sig v i μ y)
  else if s = 1 then (if x = .M ∧ y = .M then 1 else if x = .M ∨ y = .M then -1 else 1)
  else if (x = .V ∧ y = .M) ∨ (x = .M ∧ y = .V) then 1
  else if x = .V ∨ y = .V then -1 else 0

/-- The coefficient vectors of the linear forms in `[G_{xy}]^s` (Definition 8.6). -/
def brackForms (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    List (Fin M → ℂ) :=
  if s = 0 then []
  else if s = 1 then
    (if x = .M then [] else [colC Sig A z (letVec Sig v i μ x) μ]) ++
      (if y = .M then [] else [rowC Sig A z (letVec Sig v i μ y) μ])
  else if x = .V then (if y = .M then [] else [rowC Sig A z (letVec Sig v i μ y) μ])
  else if y = .V then (if x = .M then [] else [colC Sig A z (letVec Sig v i μ x) μ]) else []

/-- Definition 8.6: `[G_{xy}]^s` for `x, y` not both `V`. -/
def brack (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) : ℂ :=
  brackScal Sig A z v i μ x y s *
    ((brackForms Sig A z v i μ x y s).map fun c => linForm c fun j => A j μ).prod

section Helpers

private theorem brackets_ent_eq {p : Type*} [Fintype p] (B : Matrix p p ℂ) (x y : p → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem brackets_ent_eI_right {p : Type*} [Fintype p] [DecidableEq p] (B : Matrix p p ℂ)
    (x : p → ℝ) (r : p) : ent B x (eI r) = ∑ s, (x s : ℂ) * B s r := by
  rw [brackets_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem brackets_ent_eI_left {p : Type*} [Fintype p] [DecidableEq p] (B : Matrix p p ℂ)
    (y : p → ℝ) (r : p) : ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [brackets_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

variable (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (μ : Fin N)

private theorem brackets_eI_self (r : Fin M ⊕ Fin N) : eI r r = 1 := by simp [eI]

private theorem brackets_eI_inl_inr (i : Fin M) : eI (Sum.inl i : Fin M ⊕ Fin N) (Sum.inr μ) = 0 := by
  simp [eI]

private theorem brackets_Gmu_row (t : Fin M ⊕ Fin N) : Gmu Sig A z μ (Sum.inr μ) t = 0 := by
  simp [Gmu, G1, Gm]

private theorem brackets_Gmu_col (s : Fin M ⊕ Fin N) : Gmu Sig A z μ s (Sum.inr μ) = 0 := by
  simp [Gmu, G1, Gm]

private theorem brackets_ent_M_left (y : Fin M ⊕ Fin N → ℝ) :
    ent (Gmu Sig A z μ) (eI (Sum.inr μ)) y = 0 := by
  rw [brackets_ent_eI_left]; simp [brackets_Gmu_row]

private theorem brackets_ent_M_right (x : Fin M ⊕ Fin N → ℝ) :
    ent (Gmu Sig A z μ) x (eI (Sum.inr μ)) = 0 := by
  rw [brackets_ent_eI_right]; simp [brackets_Gmu_col]

private theorem brackets_colC_M (j : Fin M) : colC Sig A z (eI (Sum.inr μ)) μ j = 0 := by
  simp [colC, brackets_ent_M_left]

private theorem brackets_rowC_M (j : Fin M) : rowC Sig A z (eI (Sum.inr μ)) μ j = 0 := by
  simp [rowC, brackets_ent_M_right]

private theorem brackets_linForm_colC_M :
    linForm (colC Sig A z (eI (Sum.inr μ)) μ) (fun j => A j μ) = 0 := by
  simp [linForm, brackets_colC_M]

private theorem brackets_linForm_rowC_M :
    linForm (rowC Sig A z (eI (Sum.inr μ)) μ) (fun j => A j μ) = 0 := by
  simp [linForm, brackets_rowC_M]

private theorem brackets_GX_apply (s : Fin M ⊕ Fin N) :
    (G1 Sig A z (Sum.inr μ) * Xhat A) s (Sum.inr μ)
      = ∑ j, G1 Sig A z (Sum.inr μ) s (Sum.inl j) * (A j μ : ℂ) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]

private theorem brackets_ent_GX (x : Fin M ⊕ Fin N → ℝ) :
    ent (G1 Sig A z (Sum.inr μ) * Xhat A) x (eI (Sum.inr μ))
      = linForm (colC Sig A z x μ) (fun j => A j μ) := by
  rw [brackets_ent_eI_right]
  simp only [brackets_GX_apply, linForm, colC, Gmu, brackets_ent_eI_right, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

private theorem brackets_XtG_apply (t : Fin M ⊕ Fin N) :
    ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (Sum.inr μ) t
      = ∑ j, (A j μ : ℂ) * G1 Sig A z (Sum.inr μ) (Sum.inl j) t := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Xhat, cplx]

private theorem brackets_ent_XtG (y : Fin M ⊕ Fin N → ℝ) :
    ent ((Xhat A)ᵀ * G1 Sig A z (Sum.inr μ)) (eI (Sum.inr μ)) y
      = linForm (rowC Sig A z y μ) (fun j => A j μ) := by
  rw [brackets_ent_eI_left]
  simp only [brackets_XtG_apply, linForm, rowC, Gmu, brackets_ent_eI_left, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end Helpers

/-- (G_split): `G_{xy} = [G_{xy}]^0 + G_μμ [G_{xy}]^1 + v̄(μ) G_μμ [G_{xy}]^2`, `x, y` not both `V`;
from (main_identity). -/
theorem G_split {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (x y : Letter) (hxy : ¬(x = .V ∧ y = .V)) :
    ent (G Sig A z) (letVec Sig v i μ x) (letVec Sig v i μ y) =
      brack Sig A z v i μ x y 0 + G Sig A z (Sum.inr μ) (Sum.inr μ) * brack Sig A z v i μ x y 1 +
        ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) * G Sig A z (Sum.inr μ) (Sum.inr μ) *
          brack Sig A z v i μ x y 2 := by
  have hmain := main_identity hSig A hz μ (letVec Sig v i μ x) (letVec Sig v i μ y)
  rw [brackets_ent_GX, brackets_ent_XtG] at hmain
  rw [hmain]
  cases x <;> cases y
  · exact absurd ⟨rfl, rfl⟩ hxy
  all_goals
    simp [letVec, brack, brackScal, brackForms, brackets_eI_self, brackets_eI_inl_inr,
      brackets_ent_M_left, brackets_ent_M_right,
      brackets_linForm_colC_M, brackets_linForm_rowC_M]
    try ring

/-- The zero brackets vanish. -/
theorem brack_eq_zero (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3)
    (h : zeroTab x y s = true) : brack Sig A z v i μ x y s = 0 := by
  fin_cases s <;> cases x <;> cases y <;>
    simp_all [zeroTab, brack, brackScal, brackForms, letVec, brackets_ent_M_left,
      brackets_ent_M_right]

/-- The number of linear forms of `[G_{xy}]^s` is its degree. -/
theorem brackForms_length (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ)
    (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    (brackForms Sig A z v i μ x y s).length = degTab x y s := by
  fin_cases s <;> cases x <;> cases y <;> simp [brackForms, degTab]

/-- The parity rule behind Lemma 8.10: `deg [G_{xy}]^s ≡ #{M in x, y} + [s = 2]` on nonzero
brackets. -/
theorem degTab_parity (x y : Letter) (s : Fin 3) (hxy : ¬(x = .V ∧ y = .V))
    (hz : zeroTab x y s = false) :
    (degTab x y s + nMu x y + (if s = 2 then 1 else 0)) % 2 = 0 := by
  revert x y s; decide

section WardHelpers

/-- `‖(1 : Matrix b b ℝ).submatrix f id‖ ≤ 1` for injective `f`. -/
private theorem brackets_norm_sel {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (f : a → b) (hf : Function.Injective f) : ‖(1 : Matrix b b ℝ).submatrix f id‖ ≤ 1 := by
  classical
  set P := (1 : Matrix b b ℝ).submatrix f id with hP
  have h1 : P * Pᴴ = 1 := by
    ext x y
    simp only [hP, mul_apply, submatrix_apply, conjTranspose_apply, star_trivial, one_apply, id]
    rw [Finset.sum_eq_single (f x)]
    · by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy, hf.ne hxy, eq_comm]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have h2 : ‖Pᴴ‖ * ‖Pᴴ‖ ≤ 1 := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose, h1]
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  rw [l2_opNorm_conjTranspose] at h2
  nlinarith [norm_nonneg P]

/-- `‖A|‖ ≤ ‖A‖` for a submatrix along injective maps. -/
private theorem brackets_norm_submatrix {a b m' n' : Type*} [Fintype a] [Fintype b] [Fintype m']
    [Fintype n'] [DecidableEq b] [DecidableEq n'] (A : Matrix m' n' ℝ) (f : a → m') (g : b → n')
    (hf : Function.Injective f) (hg : Function.Injective g) : ‖A.submatrix f g‖ ≤ ‖A‖ := by
  classical
  have e : A.submatrix f g
      = (1 : Matrix m' m' ℝ).submatrix f id * A * ((1 : Matrix n' n' ℝ).submatrix g id)ᴴ := by
    ext x y
    simp only [mul_apply, submatrix_apply, conjTranspose_apply, star_trivial, one_apply, id,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_ite, mul_one,
      mul_zero]
  rw [e]
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose]
  refine (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)).trans ?_
  have h1 := brackets_norm_sel f hf
  have h2 := brackets_norm_sel g hg
  calc ‖(1 : Matrix m' m' ℝ).submatrix f id‖ * ‖A‖ * ‖(1 : Matrix n' n' ℝ).submatrix g id‖
      ≤ 1 * ‖A‖ * 1 := by gcongr
    _ = ‖A‖ := by ring

/-- `‖A|ᵀ A|‖ ≤ ‖Aᵀ A‖` for a submatrix along injective maps. -/
private theorem brackets_norm_XtX_submatrix {a b m' n' : Type*} [Fintype a] [Fintype b]
    [Fintype m'] [Fintype n'] [DecidableEq b] [DecidableEq n'] (A : Matrix m' n' ℝ) (f : a → m')
    (g : b → n') (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖(A.submatrix f g)ᵀ * A.submatrix f g‖ ≤ ‖Aᵀ * A‖ := by
  classical
  rw [← conjTranspose_eq_transpose_of_trivial, ← conjTranspose_eq_transpose_of_trivial,
    l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose_mul_self]
  have h := brackets_norm_submatrix A f g hf hg
  exact mul_self_le_mul_self (norm_nonneg _) h

/-- Sum over `p` of a function vanishing on `P`, as a sum over the complement subtype. -/
private theorem brackets_sum_dite {p R : Type*} [Fintype p] [AddCommMonoid R] (P : p → Prop)
    [DecidablePred P] (f : {i // ¬ P i} → R) :
    ∑ i, (if h : P i then 0 else f ⟨i, h⟩) = ∑ j, f j := by
  have h := Finset.sum_subtype (Finset.univ.filter (fun i => ¬ P i)) (p := fun i => ¬ P i)
    (F := inferInstance) (by simp) (fun i => if h : P i then 0 else f ⟨i, h⟩)
  rw [Finset.sum_filter] at h
  have h1 : ∑ i, (if ¬ P i then (if h : P i then (0 : R) else f ⟨i, h⟩) else 0)
      = ∑ i, (if h : P i then 0 else f ⟨i, h⟩) :=
    Finset.sum_congr rfl fun i _ => by by_cases hi : P i <;> simp [hi]
  rw [h1] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => by simp [j.2]

/-- Restriction of a real vector on `𝓘` to `𝓘 ∖ S`. -/
private def bracketsRes (S : Finset (Fin M ⊕ Fin N)) (x : Fin M ⊕ Fin N → ℝ) :
    idxM S ⊕ idxN S → ℝ :=
  Sum.elim (fun i => x (Sum.inl i.1)) (fun μ => x (Sum.inr μ.1))

/-- The row vector `xᵀ (extend S B)`. -/
private theorem brackets_vecMul_extend (S : Finset (Fin M ⊕ Fin N))
    (B : Matrix (idxM S ⊕ idxN S) (idxM S ⊕ idxN S) ℂ) (x : Fin M ⊕ Fin N → ℝ)
    (t : Fin M ⊕ Fin N) :
    (cvec x ᵥ* extend S B) t
      = if ht : t ∈ S then 0 else (cvec (bracketsRes S x) ᵥ* B) (toSub S t ht) := by
  by_cases ht : t ∈ S
  · simp [vecMul, dotProduct, extend, ht]
  · simp only [ht, dite_false, vecMul, dotProduct, Fintype.sum_sum_type, bracketsRes]
    have e1 := brackets_sum_dite (fun i : Fin M => Sum.inl i ∈ S)
      (fun j : idxM S => (x (Sum.inl j.1) : ℂ) * B (Sum.inl j) (toSub S t ht))
    have e2 := brackets_sum_dite (fun μ : Fin N => Sum.inr μ ∈ S)
      (fun j : idxN S => (x (Sum.inr j.1) : ℂ) * B (Sum.inr j) (toSub S t ht))
    simp only [cvec, Sum.elim_inl, Sum.elim_inr, extend]
    rw [← e1, ← e2]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by by_cases hi : Sum.inl i ∈ S <;> simp [hi, ht, toSub]
    · exact Finset.sum_congr rfl fun i _ => by by_cases hi : Sum.inr i ∈ S <;> simp [hi, ht, toSub]

/-- `ent` of a zero extension is `ent` of the block on `𝓘 ∖ S`, for the restricted vectors. -/
private theorem brackets_ent_extend (S : Finset (Fin M ⊕ Fin N))
    (B : Matrix (idxM S ⊕ idxN S) (idxM S ⊕ idxN S) ℂ) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (extend S B) x y = ent B (bracketsRes S x) (bracketsRes S y) := by
  have h1 : ent (extend S B) x y = ∑ t, (cvec x ᵥ* extend S B) t * (y t : ℂ) := by
    rw [ent, dotProduct_mulVec]; rfl
  have h2 : ent B (bracketsRes S x) (bracketsRes S y)
      = ∑ t, (cvec (bracketsRes S x) ᵥ* B) t * (bracketsRes S y t : ℂ) := by
    rw [ent, dotProduct_mulVec]; rfl
  rw [h1, h2, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [brackets_vecMul_extend]
  have e1 := brackets_sum_dite (fun i : Fin M => Sum.inl i ∈ S)
    (fun j : idxM S => (cvec (bracketsRes S x) ᵥ* B) (Sum.inl j) * (bracketsRes S y (Sum.inl j) : ℂ))
  have e2 := brackets_sum_dite (fun μ : Fin N => Sum.inr μ ∈ S)
    (fun j : idxN S => (cvec (bracketsRes S x) ᵥ* B) (Sum.inr j) * (bracketsRes S y (Sum.inr j) : ℂ))
  congr 1
  · rw [← e1]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases hi : Sum.inl i ∈ S <;> simp [hi, toSub, bracketsRes]
  · rw [← e2]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases hi : Sum.inr i ∈ S <;> simp [hi, toSub, bracketsRes]

/-- The restriction of `e_j` is the unit vector of `j` in `𝓘 ∖ S`, when no `𝓘_M` index is in `S`. -/
private theorem brackets_res_eI_inl (S : Finset (Fin M ⊕ Fin N)) (hS : ∀ i, Sum.inl i ∉ S)
    (j : Fin M) : bracketsRes S (eI (Sum.inl j)) = eI (Sum.inl ⟨j, hS j⟩) := by
  funext s
  rcases s with ⟨i, hi⟩ | ⟨ν, hν⟩ <;>
    simp [bracketsRes, eI, Pi.single_apply, Subtype.ext_iff]

/-- A quadratic form transported along the identification `𝓘_M ∖ S ≃ 𝓘_M`. -/
private theorem brackets_quad_submatrix (S : Finset (Fin M ⊕ Fin N)) (hS : ∀ i, Sum.inl i ∉ S)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (u : Fin M → ℝ) :
    (u ∘ (Subtype.val : idxM S → Fin M)) ⬝ᵥ
        (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val *
          Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val) *ᵥ
          (u ∘ (Subtype.val : idxM S → Fin M)) = u ⬝ᵥ (Sig * Sig) *ᵥ u := by
  let e : idxM S ≃ Fin M := Equiv.subtypeUnivEquiv hS
  have he : (Subtype.val : idxM S → Fin M) = e := rfl
  rw [he, Matrix.submatrix_mul_equiv, Matrix.submatrix_mulVec_equiv]
  have h1 : (u ∘ e) ∘ e.symm = u := by
    funext k; simp
  rw [h1]
  simp only [dotProduct, Function.comp_apply]
  exact Equiv.sum_comp e (fun k => u k * ((Sig * Sig) *ᵥ u) k)

end WardHelpers

/-- (GMaa) for the minor `G^{(μ)}` (Lemma 4.6 for the model with column `μ` removed). -/
theorem ward_minor_M {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (x : Fin M ⊕ Fin N → ℝ) :
    ∑ j, ‖colC Sig A z x μ j‖ ^ 2 ≤
      2 * ‖Sig‖ ^ 2 * ‖Aᵀ * A‖ / z.im * (ent (Gmu Sig A z μ) x x).im +
        2 * ((x ∘ Sum.inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ Sum.inl)) := by
  set S : Finset (Fin M ⊕ Fin N) := {Sum.inr μ} with hSdef
  have hS : ∀ i, Sum.inl i ∉ S := by simp [hSdef]
  have hinjM : Function.Injective (Subtype.val : idxM S → Fin M) := Subtype.val_injective
  have hinjN : Function.Injective (Subtype.val : idxN S → Fin N) := Subtype.val_injective
  have hP : (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val).PosDef :=
    hSig.submatrix hinjM
  have hG : Gmu Sig A z μ = extend S (G (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val)
      (A.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)) z) :=
    Gm_eq_extend_G_of_subset_N Sig A z S hS
  have hgm := GMaa_unified hP
    (A.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)) hz
    (bracketsRes S x)
  have hc : ∀ j : Fin M, colC Sig A z x μ j
      = ent (G (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val)
        (A.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)) z)
        (bracketsRes S x) (eI (Sum.inl ⟨j, hS j⟩)) := by
    intro j
    rw [colC, hG, brackets_ent_extend, brackets_res_eI_inl S hS j]
  have hl : ∑ j, ‖colC Sig A z x μ j‖ ^ 2
      = ∑ j' : idxM S, ‖ent (G (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val)
        (A.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)) z)
        (bracketsRes S x) (eI (Sum.inl j'))‖ ^ 2 := by
    simp only [hc]
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv hS).symm _ _ (fun j => rfl)
  have hIm : (ent (G (Sig.submatrix (Subtype.val : idxM S → Fin M) Subtype.val)
        (A.submatrix (Subtype.val : idxM S → Fin M) (Subtype.val : idxN S → Fin N)) z)
        (bracketsRes S x) (bracketsRes S x)) = ent (Gmu Sig A z μ) x x := by
    rw [hG, brackets_ent_extend]
  have hq := brackets_quad_submatrix S hS Sig (x ∘ Sum.inl)
  have hq' : (bracketsRes S x ∘ Sum.inl) = (x ∘ Sum.inl) ∘ (Subtype.val : idxM S → Fin M) := rfl
  rw [hq', hq, hIm] at hgm
  have hnn : 0 ≤ (ent (Gmu Sig A z μ) x x).im := by
    have h := GMaa4_minor hSig A hz S x
    have h0 : 0 ≤ (ent (Gm Sig A z S) x x).im / z.im := by
      rw [← h]; positivity
    have := mul_nonneg h0 hz.le
    rwa [div_mul_cancel₀ _ hz.ne'] at this
  have hn1 := brackets_norm_submatrix Sig (Subtype.val : idxM S → Fin M) Subtype.val hinjM hinjM
  have hn2 := brackets_norm_XtX_submatrix A (Subtype.val : idxM S → Fin M)
    (Subtype.val : idxN S → Fin N) hinjM hinjN
  rw [hl]
  refine hgm.trans ?_
  have hz' : 0 < z.im := hz
  gcongr

private theorem brackets_extend_transpose {S : Finset (Fin M ⊕ Fin N)}
    {B : Matrix (idxM S ⊕ idxN S) (idxM S ⊕ idxN S) ℂ} (hB : Bᵀ = B) :
    (extend S B)ᵀ = extend S B := by
  ext s t
  simp only [Matrix.transpose_apply, extend]
  by_cases hs : s ∈ S <;> by_cases ht : t ∈ S
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht]
  · simp only [hs, ht, dite_false]
    exact congrFun (congrFun hB (toSub S s hs)) (toSub S t ht)

/-- `G^{(μ)}` is complex symmetric. -/
theorem Gmu_transpose {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) :
    (Gmu Sig A z μ)ᵀ = Gmu Sig A z μ := by
  have hS : ∀ i, Sum.inl i ∉ ({Sum.inr μ} : Finset (Fin M ⊕ Fin N)) := by simp
  have hP := hSig.submatrix (Subtype.val_injective
    (p := fun i : Fin M => Sum.inl i ∉ ({Sum.inr μ} : Finset (Fin M ⊕ Fin N))))
  have hT := G_transpose hP
    (A.submatrix (Subtype.val : idxM ({Sum.inr μ} : Finset (Fin M ⊕ Fin N)) → Fin M)
      (Subtype.val : idxN ({Sum.inr μ} : Finset (Fin M ⊕ Fin N)) → Fin N)) hz
  rw [Gmu, G1, Gm_eq_extend_G_of_subset_N Sig A z _ hS]
  exact brackets_extend_transpose hT

/-- The factors of `𝐢𝛍` are `G_{v̄ i}` and `G_{μ v̄}`. -/
example : factorX (k := 0) (fun _ => true) 0 = .V ∧ factorY (k := 0) (fun _ => true) 0 = .I ∧
    factorX (k := 0) (fun _ => true) 1 = .M ∧ factorY (k := 0) (fun _ => true) 1 = .V := by
  decide

/-! ### Compiled instances at `M = N = 2`, `z = i` -/

section Checks

open Complex

/-- The vector `v = (1, 1, 1, 1)` on `𝓘 = Fin 2 ⊕ Fin 2`. -/
local notation "v1" => (fun _ => (1 : ℝ) : Fin 2 ⊕ Fin 2 → ℝ)

/-- (G_split) at `Σ = 1`, `X = 0`, `z = i`, `μ = 0`, the pair `(V, I)`. -/
example :
    ent (G (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I)
        (letVec (diagonal fun _ : Fin 2 => (1 : ℝ)) v1 0 0 .V)
        (letVec (diagonal fun _ : Fin 2 => (1 : ℝ)) v1 0 0 .I) =
      brack (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I v1 0 0
          .V .I 0 +
        G (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I (Sum.inr 0)
            (Sum.inr 0) *
          brack (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I v1
            0 0 .V .I 1 +
        ((vbar (diagonal fun _ : Fin 2 => (1 : ℝ)) v1 (Sum.inr 0) : ℝ) : ℂ) *
          G (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I (Sum.inr 0)
            (Sum.inr 0) *
          brack (diagonal fun _ : Fin 2 => (1 : ℝ)) (0 : Matrix (Fin 2) (Fin 2) ℝ) I v1
            0 0 .V .I 2 :=
  G_split (posDef_diagonal_iff.2 fun _ => one_pos) 0 (by simp) v1 0 0 .V .I (by decide)

/-- The parity rule at `[G_{VM}]^2`. -/
example : (degTab .V .M 2 + nMu .V .M + (if (2 : Fin 3) = 2 then 1 else 0)) % 2 = 0 :=
  degTab_parity .V .M 2 (by decide) (by decide)

end Checks

end Anisotropic
