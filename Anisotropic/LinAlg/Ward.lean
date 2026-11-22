module

public import Anisotropic.LinAlg.Blocks
public import Anisotropic.LinAlg.Minor

@[expose] public section

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

/-- Operator-norm bound on sums of squares for a real vector. -/
private theorem ward_real_norm {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (A : Matrix p q ℝ) (u : q → ℝ) :
    ∑ i, (A *ᵥ u) i ^ 2 ≤ ‖A‖ ^ 2 * ∑ μ, u μ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 u)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

/-- Operator-norm bound on sums of squared moduli for a complex vector and a real matrix. -/
private theorem ward_cplx_norm {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (A : Matrix p q ℝ) (r : q → ℂ) :
    ∑ i, ‖(cplx A *ᵥ r) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ μ, ‖r μ‖ ^ 2 := by
  have hre : ∀ i, ((cplx A *ᵥ r) i).re = (A *ᵥ fun μ => (r μ).re) i := by
    intro i
    simp [mulVec, dotProduct, cplx, Complex.re_sum]
  have him : ∀ i, ((cplx A *ᵥ r) i).im = (A *ᵥ fun μ => (r μ).im) i := by
    intro i
    simp [mulVec, dotProduct, cplx, Complex.im_sum]
  have e1 : ∑ i, ‖(cplx A *ᵥ r) i‖ ^ 2
      = ∑ i, (A *ᵥ fun μ => (r μ).re) i ^ 2 + ∑ i, (A *ᵥ fun μ => (r μ).im) i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply, ← hre, ← him]; ring
  have e2 : ∑ μ, ‖r μ‖ ^ 2 = ∑ μ, (r μ).re ^ 2 + ∑ μ, (r μ).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [e1, e2, mul_add]
  exact add_le_add (ward_real_norm A _) (ward_real_norm A _)

/-- Row-vector form of `ward_cplx_norm`. -/
private theorem ward_cplx_norm_vecMul {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (A : Matrix q p ℝ) (r : q → ℂ) :
    ∑ i, ‖(r ᵥ* cplx A) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ μ, ‖r μ‖ ^ 2 := by
  have h := ward_cplx_norm Aᵀ r
  have e : cplx Aᵀ = (cplx A)ᵀ := by ext i j; simp [cplx]
  have hn : ‖Aᵀ‖ = ‖A‖ := by
    have := Matrix.l2_opNorm_conjTranspose A
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  rw [e, mulVec_transpose, hn] at h
  exact h

/-- `(linH A X z)ᴴ - linH A X z = 2 i Im z · P_N` for a real symmetric `A`. -/
private theorem ward_linH_sub {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix p p ℝ} (hA : Aᵀ = A) (X : Matrix p q ℝ) (z : ℂ) :
    (linH A X z)ᴴ - linH A X z
      = ((2 * z.im : ℝ) * Complex.I) • (PN : Matrix (p ⊕ q) (p ⊕ q) ℂ) := by
  have hAc : (cplx A)ᴴ = cplx A := by
    ext i j
    have := congrFun (congrFun hA i) j
    simp [cplx, conjTranspose_apply]
    exact this
  have hX : (cplx X)ᴴ = cplx Xᵀ := by ext i j; simp [cplx]
  have hXt : (cplx Xᵀ)ᴴ = cplx X := by ext i j; simp [cplx]
  rw [linH, fromBlocks_conjTranspose, PN, fromBlocks_smul, sub_eq_add_neg,
    fromBlocks_neg, fromBlocks_add]
  congr 1
  · simp [hAc]
  · simp [hXt]
  · simp [hX]
  · ext i j
    simp [one_apply, Matrix.smul_apply]
    split_ifs
    · have := Complex.sub_conj z
      push_cast at this
      linear_combination this
    · simp


/-- Ward identity for the inverse of `linH A X z`: `B - Bᴴ = 2 i Im z · B P_N Bᴴ`. -/
private theorem ward_GA_sub {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix p p ℝ} (hA : A.PosDef) (X : Matrix p q ℝ) {z : ℂ} (hz : 0 < z.im) :
    GA A X z - (GA A X z)ᴴ
      = ((2 * z.im : ℝ) * Complex.I) •
        (GA A X z * (PN : Matrix (p ⊕ q) (p ⊕ q) ℂ) * (GA A X z)ᴴ) := by
  have hAt : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.1.eq
  have hu := (isUnit_iff_isUnit_det _).1 (linH_isUnit hA X hz)
  have h1 : GA A X z * linH A X z = 1 := nonsing_inv_mul _ hu
  have h1' : (linH A X z)ᴴ * (GA A X z)ᴴ = 1 := by
    rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : GA A X z * ((linH A X z)ᴴ - linH A X z) * (GA A X z)ᴴ
      = GA A X z - (GA A X z)ᴴ := by
    have e1 : GA A X z * (linH A X z)ᴴ * (GA A X z)ᴴ = GA A X z := by
      rw [Matrix.mul_assoc, h1', Matrix.mul_one]
    have e2 : GA A X z * linH A X z * (GA A X z)ᴴ = (GA A X z)ᴴ := by
      rw [h1, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [← key, ward_linH_sub hAt, Matrix.mul_smul, Matrix.smul_mul]

/-- `ent B x (e_t)` is the `t`-th entry of the row vector `xᵀ B`. -/
private theorem ward_ent_eI {p : Type*} [Fintype p] [DecidableEq p] (B : Matrix p p ℂ)
    (x : p → ℝ) (t : p) : ent B x (eI t) = (cvec x ᵥ* B) t := by
  simp [ent, eI, cvec, dotProduct, mulVec, vecMul, Pi.single_apply, apply_ite,
    Finset.sum_ite_eq', mul_comm]

/-- `ent` of the conjugate transpose is the conjugate of `ent` with the arguments swapped. -/
private theorem ward_ent_conjTranspose {p : Type*} [Fintype p] (B : Matrix p p ℂ) (x y : p → ℝ) :
    ent Bᴴ x y = star (ent B y x) := by
  simp only [ent, dotProduct, mulVec, conjTranspose_apply, star_sum, star_mul', cvec,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm, mul_left_comm]

private theorem ward_ent_sandwich {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (B : Matrix (p ⊕ q) (p ⊕ q) ℂ) (y : p ⊕ q → ℝ) :
    ent (B * (PN : Matrix (p ⊕ q) (p ⊕ q) ℂ) * Bᴴ) y y
      = ((∑ μ, ‖ent B y (eI (inr μ))‖ ^ 2 : ℝ) : ℂ) := by
  have h : ent (B * (PN : Matrix (p ⊕ q) (p ⊕ q) ℂ) * Bᴴ) y y
      = (cvec y ᵥ* B) ⬝ᵥ ((PN : Matrix (p ⊕ q) (p ⊕ q) ℂ) *ᵥ (Bᴴ *ᵥ cvec y)) := by
    rw [ent, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  have hs : star (cvec y) = cvec y := by ext s; simp [cvec]
  have hc : Bᴴ *ᵥ cvec y = star (cvec y ᵥ* B) := by
    rw [star_vecMul, hs]
  rw [h, hc]
  simp only [dotProduct, Fintype.sum_sum_type, PN, fromBlocks_mulVec]
  simp [ward_ent_eI, mul_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact Complex.mul_conj' _

/-- Scalar Ward identity for the inverse of `linH A X z`: for real `y`,
`Im (yᵀ B y) = Im z · ∑_μ |(yᵀ B)_μ|²`. -/
private theorem ward_GA_scalar {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix p p ℝ} (hA : A.PosDef) (X : Matrix p q ℝ) {z : ℂ} (hz : 0 < z.im)
    (y : p ⊕ q → ℝ) :
    (ent (GA A X z) y y).im = z.im * ∑ μ, ‖ent (GA A X z) y (eI (inr μ))‖ ^ 2 := by
  have h := congrArg (fun M => ent M y y) (ward_GA_sub hA X hz)
  have e1 : ent (GA A X z - (GA A X z)ᴴ) y y = ent (GA A X z) y y - star (ent (GA A X z) y y) := by
    rw [← ward_ent_conjTranspose]
    simp [ent, sub_mulVec, dotProduct_sub]
  have e2 : ent (((2 * z.im : ℝ) * Complex.I) •
        (GA A X z * (PN : Matrix (p ⊕ q) (p ⊕ q) ℂ) * (GA A X z)ᴴ)) y y
      = ((2 * z.im : ℝ) * Complex.I) *
        ((∑ μ, ‖ent (GA A X z) y (eI (inr μ))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← ward_ent_sandwich]
    simp [ent, smul_mulVec, dotProduct_smul]
  simp only [e1, e2] at h
  generalize (∑ μ, ‖ent (GA A X z) y (eI (inr μ))‖ ^ 2 : ℝ) = Sr at h ⊢
  have := congrArg Complex.im h
  simp [Complex.sub_im] at this
  linarith

/-- Sum over `p` of a function vanishing on `P`, as a sum over the complement subtype. -/
private theorem ward_sum_dite {p M : Type*} [Fintype p] [AddCommMonoid M] (P : p → Prop)
    [DecidablePred P] (f : {i // ¬ P i} → M) :
    ∑ i, (if h : P i then 0 else f ⟨i, h⟩) = ∑ j, f j := by
  have h := Finset.sum_subtype (Finset.univ.filter (fun i => ¬ P i)) (p := fun i => ¬ P i)
    (F := inferInstance) (by simp) (fun i => if h : P i then 0 else f ⟨i, h⟩)
  rw [Finset.sum_filter] at h
  have h1 : ∑ i, (if ¬ P i then (if h : P i then (0 : M) else f ⟨i, h⟩) else 0)
      = ∑ i, (if h : P i then 0 else f ⟨i, h⟩) :=
    Finset.sum_congr rfl fun i _ => by by_cases hi : P i <;> simp [hi]
  rw [h1] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => by simp [j.2]

/-- Restriction of a real vector on `𝓘` to `𝓘 ∖ S`. -/
private def wardRes (S : Finset (m ⊕ n)) (x : m ⊕ n → ℝ) : idxM S ⊕ idxN S → ℝ :=
  Sum.elim (fun i => x (inl i.1)) (fun μ => x (inr μ.1))

/-- The row vector `xᵀ (extend S B)`. -/
private theorem ward_vecMul_extend (S : Finset (m ⊕ n))
    (B : Matrix (idxM S ⊕ idxN S) (idxM S ⊕ idxN S) ℂ) (x : m ⊕ n → ℝ) (t : m ⊕ n) :
    (cvec x ᵥ* extend S B) t
      = if ht : t ∈ S then 0 else (cvec (wardRes S x) ᵥ* B) (toSub S t ht) := by
  by_cases ht : t ∈ S
  · simp [vecMul, dotProduct, extend, ht]
  · simp only [ht, dite_false, vecMul, dotProduct, Fintype.sum_sum_type, wardRes]
    have e1 := ward_sum_dite (fun i : m => inl i ∈ S)
      (fun j : idxM S => (x (inl j.1) : ℂ) * B (inl j) (toSub S t ht))
    have e2 := ward_sum_dite (fun μ : n => inr μ ∈ S)
      (fun j : idxN S => (x (inr j.1) : ℂ) * B (inr j) (toSub S t ht))
    simp only [cvec, Sum.elim_inl, Sum.elim_inr, extend]
    rw [← e1, ← e2]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by by_cases hi : inl i ∈ S <;> simp [hi, ht, toSub]
    · exact Finset.sum_congr rfl fun i _ => by by_cases hi : inr i ∈ S <;> simp [hi, ht, toSub]

/-- `ent` of a zero extension is `ent` of the block on `𝓘 ∖ S`, for the restricted vector. -/
private theorem ward_ent_extend (S : Finset (m ⊕ n))
    (B : Matrix (idxM S ⊕ idxN S) (idxM S ⊕ idxN S) ℂ) (x : m ⊕ n → ℝ) :
    ent (extend S B) x x = ent B (wardRes S x) (wardRes S x) := by
  have h1 : ent (extend S B) x x = ∑ t, (cvec x ᵥ* extend S B) t * (x t : ℂ) := by
    rw [ent, dotProduct_mulVec]; rfl
  have h2 : ent B (wardRes S x) (wardRes S x)
      = ∑ t, (cvec (wardRes S x) ᵥ* B) t * (wardRes S x t : ℂ) := by
    rw [ent, dotProduct_mulVec]; rfl
  rw [h1, h2, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [ward_vecMul_extend]
  have e1 := ward_sum_dite (fun i : m => inl i ∈ S)
    (fun j : idxM S => (cvec (wardRes S x) ᵥ* B) (inl j) * (wardRes S x (inl j) : ℂ))
  have e2 := ward_sum_dite (fun μ : n => inr μ ∈ S)
    (fun j : idxN S => (cvec (wardRes S x) ᵥ* B) (inr j) * (wardRes S x (inr j) : ℂ))
  congr 1
  · rw [← e1]
    exact Finset.sum_congr rfl fun i _ => by by_cases hi : inl i ∈ S <;> simp [hi, toSub, wardRes]
  · rw [← e2]
    exact Finset.sum_congr rfl fun i _ => by by_cases hi : inr i ∈ S <;> simp [hi, toSub, wardRes]

/-- Ward identity for every minor, any real vector. -/
private theorem ward_minor {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (S : Finset (m ⊕ n)) (x : m ⊕ n → ℝ) :
    ∑ μ, ‖ent (Gm Sig X z S) x (eI (inr μ))‖ ^ 2 = (ent (Gm Sig X z S) x x).im / z.im := by
  rw [Gm_eq_extend, ward_ent_extend]
  have hP := hSig.inv.submatrix (Subtype.val_injective (p := fun i : m => Sum.inl i ∉ S))
  have key := ward_GA_scalar hP
    (X.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxN S → n)) hz (wardRes S x)
  rw [eq_div_iff hz.ne', mul_comm, key]
  congr 1
  have e := ward_sum_dite (fun μ : n => inr μ ∈ S)
    (fun j : idxN S => ‖ent (GA (Sig⁻¹.submatrix (Subtype.val : idxM S → m) Subtype.val)
      (X.submatrix (Subtype.val : idxM S → m) (Subtype.val : idxN S → n)) z) (wardRes S x)
        (eI (inr j))‖ ^ 2)
  rw [← e]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases hμ : inr μ ∈ S
  · simp [ward_ent_eI, ward_vecMul_extend, hμ]
  · simp only [ward_ent_eI, ward_vecMul_extend, hμ, dite_false]
    rfl

/-- Complexification is multiplicative. -/
private theorem ward_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B :=
  Matrix.map_mul (f := algebraMap ℝ ℂ)

/-- Rows of `G` on `𝓘_M`, from the first form of (G=G): the `𝓘_M` entries of `xᵀG` are
`r Xᵀ Σ - (xᵀ|_M) Σ` with `r` the `𝓘_N` entries of `xᵀG`. -/
private theorem ward_rowM {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (x : m ⊕ n → ℝ) (i : m) :
    ent (G Sig X z) x (eI (inl i))
      = ((fun μ => ent (G Sig X z) x (eI (inr μ))) ᵥ* cplx (Xᵀ * Sig)) i
        - (cvec (x ∘ inl) ᵥ* cplx Sig) i := by
  have hG := (GeqG hSig X hz).1
  have hr : (fun μ => ent (G Sig X z) x (eI (inr μ)))
      = cvec (x ∘ inl) ᵥ* (cplx Sig * cplx X * GN Sig X z) + cvec (x ∘ inr) ᵥ* GN Sig X z := by
    funext μ
    rw [ward_ent_eI, hG, vecMul_fromBlocks]
    rfl
  rw [hr, ward_ent_eI, hG, vecMul_fromBlocks]
  simp only [Sum.elim_inl, Function.comp_def, Pi.sub_apply, Pi.add_apply, ward_cplx_mul,
    add_vecMul, vecMul_vecMul, Matrix.mul_assoc, vecMul_sub]
  abel

/-- `‖XᵀΣ‖² ≤ ‖Σ‖² ‖XᵀX‖`. -/
private theorem ward_XtSig_norm (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) :
    ‖Xᵀ * Sig‖ ^ 2 ≤ ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ := by
  have h1 : ‖Xᵀ * Sig‖ ≤ ‖Xᵀ‖ * ‖Sig‖ := Matrix.l2_opNorm_mul _ _
  have hX : ‖Xᵀ‖ = ‖X‖ := by
    have := Matrix.l2_opNorm_conjTranspose X
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hXX : ‖Xᵀ * X‖ = ‖X‖ * ‖X‖ := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self X
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [hXX, hX] at *
  nlinarith [h2]

/-- `∑_i |(vᵀΣ)_i|² = vᵀΣ²v` for symmetric real `Σ`. -/
private theorem ward_sum_sq_vecMul {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (v : m → ℝ) :
    ∑ i, ‖(cvec v ᵥ* cplx Sig) i‖ ^ 2 = v ⬝ᵥ (Sig * Sig) *ᵥ v := by
  have hAt : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  have e1 : ∀ i, ‖(cvec v ᵥ* cplx Sig) i‖ ^ 2 = (v ᵥ* Sig) i * (v ᵥ* Sig) i := by
    intro i
    have : (cvec v ᵥ* cplx Sig) i = (((v ᵥ* Sig) i : ℝ) : ℂ) := by
      simp [vecMul, dotProduct, cplx, cvec]
    rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]
  simp only [e1]
  have e2 : v ᵥ* Sig = Sig *ᵥ v := by rw [← mulVec_transpose, hAt]
  change (v ᵥ* Sig) ⬝ᵥ (v ᵥ* Sig) = _
  rw [← mulVec_mulVec, dotProduct_mulVec, e2]

/-- `|a - b|² ≤ 2|a|² + 2|b|²`, summed. -/
private theorem ward_sum_sub_le {p : Type*} [Fintype p] (a b : p → ℂ) :
    ∑ i, ‖a i - b i‖ ^ 2 ≤ 2 * ∑ i, ‖a i‖ ^ 2 + 2 * ∑ i, ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_sub_le (a i) (b i)
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖), norm_nonneg (a i - b i), norm_nonneg (a i),
    norm_nonneg (b i), pow_le_pow_left₀ (norm_nonneg _) h 2]

/-- (GMaa) for every real `x`, in terms of the `𝓘_N` row sum. -/
private theorem ward_rowsM_le {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (x : m ⊕ n → ℝ) :
    ∑ i, ‖ent (G Sig X z) x (eI (inl i))‖ ^ 2
      ≤ 2 * (‖Sig‖ ^ 2 * ‖Xᵀ * X‖) * ∑ μ, ‖ent (G Sig X z) x (eI (inr μ))‖ ^ 2
        + 2 * ((x ∘ inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ inl)) := by
  simp only [ward_rowM hSig X hz]
  refine (ward_sum_sub_le _ _).trans ?_
  rw [ward_sum_sq_vecMul hSig]
  have h1 := ward_cplx_norm_vecMul (Xᵀ * Sig) (fun μ => ent (G Sig X z) x (eI (inr μ)))
  have h2 := ward_XtSig_norm Sig X
  have h3 : ‖Xᵀ * Sig‖ ^ 2 * ∑ μ, ‖ent (G Sig X z) x (eI (inr μ))‖ ^ 2
      ≤ ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ * ∑ μ, ‖ent (G Sig X z) x (eI (inr μ))‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun _ _ => by positivity)
  have h4 := h1.trans h3
  rw [ward_cplx_mul] at h1
  nlinarith [h4]

/-- (GMaa3) in terms of the `𝓘_N` row sum. -/
private theorem ward_rowsM_N {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (w : n → ℝ) :
    ∑ i, ‖ent (G Sig X z) (embN w) (eI (inl i))‖ ^ 2
      ≤ ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ * ∑ μ, ‖ent (G Sig X z) (embN w) (eI (inr μ))‖ ^ 2 := by
  have h0 : cvec ((embN w : m ⊕ n → ℝ) ∘ inl) = 0 := by ext i; simp [embN, cvec]
  simp only [ward_rowM hSig X hz, h0, zero_vecMul, Pi.zero_apply, sub_zero]
  have h1 := ward_cplx_norm_vecMul (Xᵀ * Sig)
    (fun μ => ent (G Sig X z) (embN w) (eI (inr μ)))
  have h2 := ward_XtSig_norm Sig X
  have h3 : ‖Xᵀ * Sig‖ ^ 2 * ∑ μ, ‖ent (G Sig X z) (embN w) (eI (inr μ))‖ ^ 2
      ≤ ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ * ∑ μ, ‖ent (G Sig X z) (embN w) (eI (inr μ))‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun _ _ => by positivity)
  exact h1.trans h3

/-- (GMaa) for every real `x`, with the `𝓘_N` row sum eliminated by the Ward identity. -/
private theorem ward_GMaa_aux {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ)
    {z : ℂ} (hz : 0 < z.im) (x : m ⊕ n → ℝ) :
    ∑ i, ‖ent (G Sig X z) x (eI (inl i))‖ ^ 2
      ≤ 2 * ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ / z.im * (ent (G Sig X z) x x).im
        + 2 * ((x ∘ inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ inl)) := by
  have h := ward_rowsM_le hSig X hz x
  have hw := ward_minor hSig X hz ∅ x
  rw [Gm_empty] at hw
  rw [hw] at h
  have e : 2 * (‖Sig‖ ^ 2 * ‖Xᵀ * X‖) * ((ent (G Sig X z) x x).im / z.im)
      = 2 * ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ / z.im * (ent (G Sig X z) x x).im := by ring
  rw [e] at h
  exact h

section L46
variable {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
include hSig hz

/-- (GMaa4) for every real `x ∈ ℝ^𝓘`. -/
theorem GMaa4_unified (x : m ⊕ n → ℝ) :
    ∑ μ, ‖ent (G Sig X z) x (eI (inr μ))‖ ^ 2 = (ent (G Sig X z) x x).im / z.im := by
  have h := ward_minor hSig X hz ∅ x
  rwa [Gm_empty] at h

/-- (GMaa4) for every real `x` and every minor `G^{(S)}`. -/
theorem GMaa4_minor (S : Finset (m ⊕ n)) (x : m ⊕ n → ℝ) :
    ∑ μ, ‖ent (Gm Sig X z S) x (eI (inr μ))‖ ^ 2 = (ent (Gm Sig X z S) x x).im / z.im :=
  ward_minor hSig X hz S x

/-- (GMaa) for every real `x ∈ ℝ^𝓘`. -/
theorem GMaa_unified (x : m ⊕ n → ℝ) :
    ∑ i, ‖ent (G Sig X z) x (eI (inl i))‖ ^ 2
      ≤ 2 * ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ / z.im * (ent (G Sig X z) x x).im
        + 2 * ((x ∘ inl) ⬝ᵥ (Sig * Sig) *ᵥ (x ∘ inl)) :=
  ward_GMaa_aux hSig X hz x

/-- (GMaa3), `C = ‖Σ‖²`. -/
theorem GMaa3 (w : n → ℝ) :
    ∑ i, ‖ent (G Sig X z) (embN w) (eI (inl i))‖ ^ 2
      ≤ ‖Sig‖ ^ 2 * ‖Xᵀ * X‖ * ∑ μ, ‖ent (G Sig X z) (embN w) (eI (inr μ))‖ ^ 2 :=
  ward_rowsM_N hSig X hz w


end L46

end Anisotropic
