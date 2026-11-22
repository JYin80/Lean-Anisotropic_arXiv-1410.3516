module

public import Anisotropic.MainDefs
public import Mathlib

@[expose] public section

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-- `linH A X z` is invertible for `A > 0`, `Im z > 0`. -/
theorem linH_isUnit {A : Matrix m m ℝ} (hA : A.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (linH A X z) := by
  have hAc : (cplx A).IsHermitian := hA.1.map _ (fun x => by simp)
  have hAu : IsUnit (cplx A) := hA.isUnit.map (algebraMap ℝ ℂ).mapMatrix
  have hXc : (cplx X)ᴴ = cplx Xᵀ := by ext i j; simp
  rw [← mulVec_injective_iff_isUnit]
  suffices h0 : ∀ w, linH A X z *ᵥ w = 0 → w = 0 by
    intro u v huv
    exact sub_eq_zero.1 (h0 _ (by rw [mulVec_sub, huv, sub_self]))
  intro w hw
  set a := w ∘ Sum.inl
  set b := w ∘ Sum.inr
  rw [linH, fromBlocks_mulVec] at hw
  have h1 : -cplx A *ᵥ a + cplx X *ᵥ b = 0 := by
    have := congrFun hw; ext i; simpa using this (Sum.inl i)
  have h2 : cplx Xᵀ *ᵥ a + (-(z • (1 : Matrix n n ℂ))) *ᵥ b = 0 := by
    have := congrFun hw; ext i; simpa using this (Sum.inr i)
  have e1 : star a ⬝ᵥ cplx X *ᵥ b = star a ⬝ᵥ cplx A *ᵥ a := by
    have : cplx X *ᵥ b = cplx A *ᵥ a := by
      rw [neg_mulVec] at h1; linear_combination h1
    rw [this]
  have e2 : star b ⬝ᵥ cplx Xᵀ *ᵥ a = z * (star b ⬝ᵥ b) := by
    have : cplx Xᵀ *ᵥ a = z • b := by
      rw [neg_mulVec, smul_mulVec, one_mulVec] at h2; linear_combination h2
    rw [this, dotProduct_smul, smul_eq_mul]
  have e3 : star (star a ⬝ᵥ cplx X *ᵥ b) = star b ⬝ᵥ cplx Xᵀ *ᵥ a := by
    rw [star_dotProduct, star_star, star_mulVec, hXc, ← dotProduct_mulVec]
  have him : (star a ⬝ᵥ cplx A *ᵥ a).im = 0 := hAc.im_star_dotProduct_mulVec_self a
  have hbb : (star b ⬝ᵥ b).im = 0 := by
    simp [dotProduct, Complex.im_sum, Pi.star_apply, mul_comm]
  have hz0 : (z * (star b ⬝ᵥ b)).im = 0 := by
    rw [← e2, ← e3, e1, Complex.star_def, Complex.conj_im, him, neg_zero]
  rw [Complex.mul_im, hbb, mul_zero, zero_add] at hz0
  have hre : (star b ⬝ᵥ b).re = 0 := by
    rcases mul_eq_zero.1 hz0 with h | h
    · linarith
    · exact h
  have hb : b = 0 := dotProduct_star_self_eq_zero.1 (Complex.ext hre hbb)
  have ha : a = 0 := by
    rw [hb, mulVec_zero, add_zero, neg_mulVec, neg_eq_zero] at h1
    exact (mulVec_injective_iff_isUnit.2 hAu) (h1.trans (mulVec_zero _).symm)
  ext s; cases s with
  | inl i => exact congrFun ha i
  | inr μ => exact congrFun hb μ

open scoped Matrix.Norms.L2Operator
open Sum

/-- Complexification of a real vector. -/
noncomputable abbrev cvec {p : Type*} (v : p → ℝ) : p → ℂ := fun s => (v s : ℂ)

/-! ### Definition 4.2 -/

/-- `H(z)` of Definition 4.2, `fromBlocks (-Σ⁻¹) X Xᵀ (-z)`. -/
noncomputable def H (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := linH Sig⁻¹ X z

theorem G_def (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) :
    G Sig X z = (H Sig X z)⁻¹ := rfl

/-- Invertibility of `H(z)` for `Σ > 0`, `Im z > 0`. -/
theorem H_isUnit {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (H Sig X z) :=
  linH_isUnit hSig.inv X hz

theorem H_mul_G {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : H Sig X z * G Sig X z = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig X hz))

theorem G_mul_H {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : G Sig X z * H Sig X z = 1 :=
  nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig X hz))

/-- `G_M(z)`, (defGM). -/
noncomputable def GM (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) : Matrix m m ℂ :=
  (-cplx Sig⁻¹ + z⁻¹ • cplx (X * Xᵀ))⁻¹

/-- `G_N(z)`, (defGN). -/
noncomputable def GN (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) (z : ℂ) : Matrix n n ℂ :=
  (cplx (Xᵀ * Sig * X) - z • 1)⁻¹

/-- `XᵀΣX − z` is invertible for `Σ > 0`, `Im z > 0`, so `G_N(z)` of (defGN) is its inverse;
it is the Schur complement of `−Σ⁻¹` in `H(z)`. -/
theorem GN_isUnit {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (cplx (Xᵀ * Sig * X) - z • (1 : Matrix n n ℂ)) := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hS' : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  let _ : Invertible (-cplx Sig⁻¹) :=
    ⟨-cplx Sig,
      by rw [neg_mul_neg, ← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [neg_mul_neg, ← Matrix.map_mul, hS', Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have h := H_isUnit hSig X hz
  rw [H, linH, isUnit_fromBlocks_iff_of_invertible₁₁] at h
  change IsUnit (-(z • (1 : Matrix n n ℂ)) - cplx Xᵀ * (-cplx Sig) * cplx X) at h
  convert h using 1
  simp only [cplx, Matrix.map_mul, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  abel

/-- `−Σ⁻¹ + z⁻¹XXᵀ` is invertible for `Σ > 0`, `Im z > 0`, so `G_M(z)` of (defGM) is its
inverse; it is the Schur complement of `−z` in `H(z)`. -/
theorem GM_isUnit {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (-cplx Sig⁻¹ + z⁻¹ • cplx (X * Xᵀ)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  let _ : Invertible (-(z • (1 : Matrix n n ℂ))) :=
    ⟨-(z⁻¹ • 1), by simp [smul_smul, hz0], by simp [smul_smul, hz0]⟩
  have h := H_isUnit hSig X hz
  rw [H, linH, isUnit_fromBlocks_iff_of_invertible₂₂] at h
  change IsUnit (-cplx Sig⁻¹ - cplx X * (-(z⁻¹ • (1 : Matrix n n ℂ))) * cplx Xᵀ) at h
  convert h using 1
  simp only [cplx, Matrix.map_mul, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The projection `0 ⊕ 1` onto the `𝓘_N` coordinates. -/
noncomputable def PN : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 0 0 1

/-- `X` placed in the `𝓘_M × 𝓘_N` block of an `𝓘 × 𝓘` matrix (Definition 4.1 products). -/
noncomputable def Xhat (X : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 (cplx X) 0 0

/-- The `𝓘 × 𝓘_N` matrix `J = [X; 1]`. -/
def Jmat (X : Matrix m n ℝ) : Matrix (m ⊕ n) n ℝ := fromRows X 1

/-! ### Definition 4.5 and the embeddings -/

/-- `A_{vw} = ⟨v, A w⟩` for real `v, w` (Definition 4.5). -/
noncomputable def ent {p : Type*} [Fintype p] (A : Matrix p p ℂ) (v w : p → ℝ) : ℂ :=
  cvec v ⬝ᵥ A *ᵥ cvec w

/-- Standard unit vector `e_s`. -/
def eI {p : Type*} [DecidableEq p] (s : p) : p → ℝ := Pi.single s 1

/-- `v ∈ ℝ^{𝓘_M}` embedded as `(v, 0)`. -/
def embM (v : m → ℝ) : m ⊕ n → ℝ := Sum.elim v 0

/-- `w ∈ ℝ^{𝓘_N}` embedded as `(0, w)`. -/
def embN (w : n → ℝ) : m ⊕ n → ℝ := Sum.elim 0 w

theorem ent_eI_eI {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℂ) (s t : p) :
    ent A (eI s) (eI t) = A s t := by
  simp [ent, eI, cvec, dotProduct, mulVec, Pi.single_apply, apply_ite, ite_mul,
    Finset.sum_ite_eq']

theorem ent_embM_embM (A : Matrix (m ⊕ n) (m ⊕ n) ℂ) (v v' : m → ℝ) :
    ent A (embM v) (embM v') = cvec v ⬝ᵥ A.toBlocks₁₁ *ᵥ cvec v' := by
  simp [ent, embM, cvec, dotProduct, mulVec, Fintype.sum_sum_type, toBlocks₁₁]

theorem ent_embN_embN (A : Matrix (m ⊕ n) (m ⊕ n) ℂ) (w w' : n → ℝ) :
    ent A (embN w) (embN w') = cvec w ⬝ᵥ A.toBlocks₂₂ *ᵥ cvec w' := by
  simp [ent, embN, cvec, dotProduct, mulVec, Fintype.sum_sum_type, toBlocks₂₂]

/-- `G` is complex symmetric: `Gᵀ = G`. -/
theorem G_transpose {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) : (G Sig X z)ᵀ = G Sig X z := by
  have hS : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  unfold G GA
  rw [transpose_nonsing_inv]
  congr 1
  rw [linH, fromBlocks_transpose]
  congr 1
  · rw [transpose_neg, cplx, ← transpose_map, transpose_nonsing_inv, hS]
  · rw [transpose_neg, transpose_smul, transpose_one]

end Anisotropic
