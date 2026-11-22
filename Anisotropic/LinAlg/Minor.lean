module

public import Anisotropic.LinAlg.Basic

@[expose] public section

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-! ### Definition 4.3: minors -/

/-- `H^{(S)}`: rows and columns in `S` removed. -/
noncomputable def minorH (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (S : Finset (m ⊕ n)) :
    Matrix {s // s ∉ S} {s // s ∉ S} ℂ :=
  (H Sig X z).submatrix Subtype.val Subtype.val

/-- `G^{(S)} = (H^{(S)})⁻¹`. -/
noncomputable def minorG (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (S : Finset (m ⊕ n)) :
    Matrix {s // s ∉ S} {s // s ∉ S} ℂ :=
  (minorH Sig X z S)⁻¹

/-- `G^{(S)}` extended by zero to `𝓘 × 𝓘`; Definition 4.1 products of minors are
ordinary products of these. -/
noncomputable def Gm (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (S : Finset (m ⊕ n)) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := fun s t =>
  if hs : s ∈ S then 0 else if ht : t ∈ S then 0 else minorG Sig X z S ⟨s, hs⟩ ⟨t, ht⟩

/-- `G^{(r)}`. -/
noncomputable abbrev G1 (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (r : m ⊕ n) :=
  Gm Sig X z {r}

/-- `G^{(rs)}`. -/
noncomputable abbrev G2 (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (r s : m ⊕ n) :=
  Gm Sig X z {r, s}

/-- The splitting `{i // inl i ∉ S} ⊕ {μ // inr μ ∉ S} ≃ {s // s ∉ S}` of `𝓘 ∖ S` into its
`𝓘_M` and `𝓘_N` parts. -/
private def subEquiv (S : Finset (m ⊕ n)) :
    {i : m // Sum.inl i ∉ S} ⊕ {μ : n // Sum.inr μ ∉ S} ≃ {s // s ∉ S} where
  toFun := Sum.elim (fun i => ⟨inl i.1, i.2⟩) (fun μ => ⟨inr μ.1, μ.2⟩)
  invFun s := match s with
    | ⟨inl i, h⟩ => inl ⟨i, h⟩
    | ⟨inr μ, h⟩ => inr ⟨μ, h⟩
  left_inv := by rintro (i | μ) <;> rfl
  right_inv := by rintro ⟨i | μ, h⟩ <;> rfl

/-- `H^{(S)}`, reindexed by the splitting of `𝓘 ∖ S`, is the block matrix with precision block
`(Σ⁻¹)|` and `X|`. -/
private theorem minorH_submatrix_subEquiv (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ)
    (S : Finset (m ⊕ n)) :
    (minorH Sig X z S).submatrix (subEquiv S) (subEquiv S)
      = linH ((Sig⁻¹).submatrix (Subtype.val : {i : m // Sum.inl i ∉ S} → m)
          (Subtype.val : {i : m // Sum.inl i ∉ S} → m))
        (X.submatrix (Subtype.val : {i : m // Sum.inl i ∉ S} → m)
          (Subtype.val : {μ : n // Sum.inr μ ∉ S} → n)) z := by
  ext (i | μ) (j | ν) <;>
    simp [minorH, H, linH, subEquiv, one_apply, Subtype.ext_iff]

theorem minorH_isUnit {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (S : Finset (m ⊕ n)) : IsUnit (minorH Sig X z S) := by
  rw [← isUnit_submatrix_equiv (subEquiv S) (subEquiv S), minorH_submatrix_subEquiv]
  exact linH_isUnit (hSig.inv.submatrix Subtype.val_injective) _ hz

theorem Gm_empty (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    Gm Sig X z ∅ = G Sig X z := by
  let e : {s : m ⊕ n // s ∉ (∅ : Finset (m ⊕ n))} ≃ m ⊕ n :=
    Equiv.subtypeUnivEquiv (fun s => Finset.notMem_empty s)
  have h : minorG Sig X z ∅ = (G Sig X z).submatrix e e := by
    rw [minorG, G_def, ← inv_submatrix_equiv]
    rfl
  ext s t
  simp [Gm, h, e]

/-- Remaining `𝓘_M` indices. -/
abbrev idxM (S : Finset (m ⊕ n)) := {i : m // Sum.inl i ∉ S}
/-- Remaining `𝓘_N` indices. -/
abbrev idxN (S : Finset (m ⊕ n)) := {μ : n // Sum.inr μ ∉ S}

/-- An index outside `S`, as an element of `idxM S ⊕ idxN S`. -/
def toSub (S : Finset (m ⊕ n)) : (s : m ⊕ n) → s ∉ S → idxM S ⊕ idxN S
  | Sum.inl i, h => Sum.inl ⟨i, h⟩
  | Sum.inr μ, h => Sum.inr ⟨μ, h⟩

/-- Zero extension of an `(idxM S ⊕ idxN S)`-indexed matrix to `𝓘 × 𝓘`. -/
def extend (S : Finset (m ⊕ n)) (B : Matrix (idxM S ⊕ idxN S) (idxM S ⊕ idxN S) ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := fun s t =>
  if hs : s ∈ S then 0 else if ht : t ∈ S then 0 else B (toSub S s hs) (toSub S t ht)

/-- The splitting of `𝓘 ∖ S` sends `toSub S s hs` to `⟨s, hs⟩`. -/
private theorem subEquiv_toSub (S : Finset (m ⊕ n)) (s : m ⊕ n) (hs : s ∉ S) :
    subEquiv S (toSub S s hs) = ⟨s, hs⟩ := by
  cases s <;> rfl

/-- Every minor is the inverse of a matrix of the same block form, with precision
block `(Σ⁻¹)|` and `X|` (any `S`). -/
theorem Gm_eq_extend (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) (S : Finset (m ⊕ n)) :
    Gm Sig X z S = extend S (GA ((Sig⁻¹).submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m))
      (X.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxN S → n)) z) := by
  have h : GA ((Sig⁻¹).submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m))
      (X.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxN S → n)) z
        = (minorG Sig X z S).submatrix (subEquiv S) (subEquiv S) := by
    rw [GA, ← minorH_submatrix_subEquiv, inv_submatrix_equiv, minorG]
  ext s t
  unfold Gm extend
  split_ifs with hs ht
  · rfl
  · rfl
  · rw [h, submatrix_apply, subEquiv_toSub, subEquiv_toSub]

/-- `(Σ⁻¹)| = (Σ|)⁻¹` when `S ⊆ 𝓘_N`. -/
theorem inv_submatrix_of_subset_N (Sig : Matrix m m ℝ) (S : Finset (m ⊕ n))
    (hS : ∀ i, Sum.inl i ∉ S) :
    (Sig⁻¹).submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m)
      = (Sig.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m))⁻¹ := by
  let e : idxM S ≃ m := Equiv.subtypeUnivEquiv hS
  exact (inv_submatrix_equiv Sig e e).symm

/-- `(diagonal v)⁻¹ = diagonal (v⁻¹)` when every entry of `v` is nonzero. -/
private theorem inv_diagonal_of_ne_zero {p : Type*} [Fintype p] [DecidableEq p] (v : p → ℝ)
    (hv : ∀ i, v i ≠ 0) : (diagonal v)⁻¹ = diagonal (fun i => (v i)⁻¹) := by
  apply inv_eq_right_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  exact mul_inv_cancel₀ (hv i)

/-- `(Σ⁻¹)| = (Σ|)⁻¹` for diagonal `Σ` with nonzero diagonal. -/
theorem inv_submatrix_diagonal (σ : m → ℝ) (hσ : ∀ i, σ i ≠ 0) (S : Finset (m ⊕ n)) :
    ((diagonal σ)⁻¹).submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m)
      = ((diagonal σ).submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m))⁻¹ := by
  rw [inv_diagonal_of_ne_zero σ hσ, submatrix_diagonal _ _ Subtype.val_injective,
    submatrix_diagonal _ _ Subtype.val_injective,
    inv_diagonal_of_ne_zero (σ ∘ Subtype.val) (fun i => hσ i.1)]
  rfl

/-- Minor of `G` as `G` of the restricted model, `S ⊆ 𝓘_N`. -/
theorem Gm_eq_extend_G_of_subset_N (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ)
    (S : Finset (m ⊕ n)) (hS : ∀ i, Sum.inl i ∉ S) :
    Gm Sig X z S = extend S (G (Sig.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxM S → m))
      (X.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxN S → n)) z) := by
  rw [Gm_eq_extend, G, ← inv_submatrix_of_subset_N Sig S hS]

/-- Minor of `G` as `G` of the restricted model, `Σ` diagonal. -/
theorem Gm_eq_extend_G_of_diagonal (σ : m → ℝ) (hσ : ∀ i, σ i ≠ 0) (X : Matrix m n ℝ) (z : ℂ)
    (S : Finset (m ⊕ n)) :
    Gm (diagonal σ) X z S = extend S (G ((diagonal σ).submatrix (Subtype.val : idxM S → m)
      (Subtype.val : idxM S → m)) (X.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxN S → n)) z) := by
  rw [Gm_eq_extend, G, ← inv_submatrix_diagonal σ hσ S]

/-- For a real matrix `A` and a complex vector `a`, `Re(a* A a) = xᵀAx + yᵀAy` with
`x = Re a`, `y = Im a`. -/
private theorem re_star_dotProduct_cplx {p : Type*} [Fintype p] (A : Matrix p p ℝ)
    (a : p → ℂ) :
    (star a ⬝ᵥ cplx A *ᵥ a).re
      = (fun i => (a i).re) ⬝ᵥ A *ᵥ (fun i => (a i).re)
        + (fun i => (a i).im) ⬝ᵥ A *ᵥ (fun i => (a i).im) := by
  simp only [dotProduct, mulVec, Complex.re_sum, Pi.star_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, cplx, map_apply, Complex.coe_algebraMap, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A vector `a` with `a* A a = 0` for a real positive definite `A` vanishes. -/
private theorem eq_zero_of_star_dotProduct_cplx {p : Type*} [Fintype p] {A : Matrix p p ℝ}
    (hA : A.PosDef) {a : p → ℂ} (h : star a ⬝ᵥ cplx A *ᵥ a = 0) : a = 0 := by
  have hre := congrArg Complex.re h
  rw [re_star_dotProduct_cplx, Complex.zero_re] at hre
  have key : ∀ x : p → ℝ, 0 ≤ x ⬝ᵥ A *ᵥ x := fun x => by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have pos : ∀ x : p → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x := fun x hx => by
    simpa using hA.dotProduct_mulVec_pos hx
  have hx : (fun i => (a i).re) = 0 := by
    by_contra hne
    linarith [pos _ hne, key (fun i => (a i).im)]
  have hy : (fun i => (a i).im) = 0 := by
    by_contra hne
    linarith [pos _ hne, key (fun i => (a i).re)]
  ext i
  exact Complex.ext (congrFun hx i) (congrFun hy i)

/-- Diagonal entries of `(linH A X z)⁻¹` are nonzero for `A > 0`, `Im z > 0`. -/
private theorem GA_diag_ne_zero {A : Matrix m m ℝ} (hA : A.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (ρ : m ⊕ n) : GA A X z ρ ρ ≠ 0 := by
  intro h0
  have hAc : (cplx A).IsHermitian := hA.1.map _ (fun x => by simp)
  have hXc : (cplx X)ᴴ = cplx Xᵀ := by ext i j; simp
  have hBG : linH A X z * GA A X z = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (linH_isUnit hA X hz))
  set v : m ⊕ n → ℂ := fun s => GA A X z s ρ with hv
  have hBv : linH A X z *ᵥ v = Pi.single ρ 1 := by
    ext s
    have := congrFun (congrFun hBG s) ρ
    simpa [mulVec, dotProduct, mul_apply, one_apply, Pi.single_apply, hv] using this
  have hq : star v ⬝ᵥ linH A X z *ᵥ v = 0 := by
    rw [hBv]
    simp [dotProduct, Pi.single_apply, hv, h0]
  set a := v ∘ Sum.inl
  set b := v ∘ Sum.inr
  have hsplit : star v ⬝ᵥ linH A X z *ᵥ v
      = -(star a ⬝ᵥ cplx A *ᵥ a) + star a ⬝ᵥ cplx X *ᵥ b + star b ⬝ᵥ cplx Xᵀ *ᵥ a
        - z * (star b ⬝ᵥ b) := by
    rw [linH, fromBlocks_mulVec]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      Pi.star_apply, mul_add, Finset.sum_add_distrib, neg_mulVec, smul_mulVec, one_mulVec,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum,
      a, b, Function.comp_apply]
    have hz' : ∑ x, star (v (inr x)) * (z * v (inr x)) = ∑ i, z * (star (v (inr i)) * v (inr i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hz']
    ring
  have e3 : star (star a ⬝ᵥ cplx X *ᵥ b) = star b ⬝ᵥ cplx Xᵀ *ᵥ a := by
    rw [star_dotProduct, star_star, star_mulVec, hXc, ← dotProduct_mulVec]
  have him : (star a ⬝ᵥ cplx A *ᵥ a).im = 0 := hAc.im_star_dotProduct_mulVec_self a
  have hbb : (star b ⬝ᵥ b).im = 0 := by
    simp [dotProduct, Complex.im_sum, Pi.star_apply, mul_comm]
  have hcross : (star a ⬝ᵥ cplx X *ᵥ b + star b ⬝ᵥ cplx Xᵀ *ᵥ a).im = 0 := by
    rw [← e3, Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]
  have himq : (star v ⬝ᵥ linH A X z *ᵥ v).im = -(z.im * (star b ⬝ᵥ b).re) := by
    rw [Complex.add_im] at hcross
    rw [hsplit]
    simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.mul_im, him, hbb]
    linarith
  rw [hq, Complex.zero_im] at himq
  have hre : (star b ⬝ᵥ b).re = 0 := by
    rcases mul_eq_zero.1 (neg_eq_zero.1 himq.symm) with h | h
    · linarith
    · exact h
  have hb : b = 0 := dotProduct_star_self_eq_zero.1 (Complex.ext hre hbb)
  have ha : a = 0 := by
    apply eq_zero_of_star_dotProduct_cplx hA
    have := hsplit.symm.trans hq
    rw [hb] at this
    simpa using this
  have hv0 : v = 0 := by
    ext s
    cases s with
    | inl i => exact congrFun ha i
    | inr μ => exact congrFun hb μ
  have := congrFun hBv ρ
  rw [hv0, mulVec_zero] at this
  simp at this

theorem Gm_diag_ne_zero {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (S : Finset (m ⊕ n)) (r : m ⊕ n) (hr : r ∉ S) : Gm Sig X z S r r ≠ 0 := by
  rw [Gm_eq_extend]
  simp only [extend, hr, dite_false]
  exact GA_diag_ne_zero (hSig.inv.submatrix Subtype.val_injective) _ hz _

theorem G_diag_ne_zero {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (r : m ⊕ n) : G Sig X z r r ≠ 0 := by
  rw [← Gm_empty]
  exact Gm_diag_ne_zero hSig X hz ∅ r (Finset.notMem_empty r)

/-! ### Compiled checks at the instance `Σ = diag(2,1)`, `X = I/√2`, `z = i` -/

section Checks

open Complex

/-- The inclusion `idxM S → Fin 2` at `M = N = 2`. -/
local notation "ιM" S:max => (Subtype.val : idxM (S : Finset (Fin 2 ⊕ Fin 2)) → Fin 2)

/-- `σ = (2, 1)`. -/
local notation "σ0" => (![2, 1] : Fin 2 → ℝ)

end Checks

end Anisotropic
