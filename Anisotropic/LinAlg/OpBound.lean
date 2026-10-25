import Anisotropic.LinAlg.Spectral

open Matrix ComplexOrder
set_option linter.unusedSectionVars false
namespace Anisotropic
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
open scoped Matrix.Norms.L2Operator
open Sum

private theorem opb_cvec_mulVec {p q : Type*} [Fintype q] (M : Matrix p q ℝ) (v : q → ℝ) :
    cvec (M *ᵥ v) = cplx M *ᵥ cvec v := by
  funext i
  exact RingHom.map_mulVec (algebraMap ℝ ℂ) M v i

private theorem opb_ent_congr {p q : Type*} [Fintype p] [Fintype q] (R : Matrix p q ℝ)
    (M : Matrix q q ℂ) (a b : p → ℝ) :
    ent (cplx R * M * cplx Rᵀ) a b = ent M (Rᵀ *ᵥ a) (Rᵀ *ᵥ b) := by
  unfold ent
  have ht : cplx Rᵀ = (cplx R)ᵀ := by ext; rfl
  rw [opb_cvec_mulVec, opb_cvec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ht,
    mulVec_transpose, mulVec_transpose]

private theorem opb_ent_add {p : Type*} [Fintype p] (A B : Matrix p p ℂ) (a b : p → ℝ) :
    ent (A + B) a b = ent A a b + ent B a b := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem opb_ent_neg {p : Type*} [Fintype p] (A : Matrix p p ℂ) (a b : p → ℝ) :
    ent (-A) a b = -ent A a b := by
  simp [ent, neg_mulVec, dotProduct_neg]

private theorem opb_ent_cplx {p : Type*} [Fintype p] (P : Matrix p p ℝ) (a b : p → ℝ) :
    ent (cplx P) a b = ((a ⬝ᵥ P *ᵥ b : ℝ) : ℂ) := by
  rw [ent, ← opb_cvec_mulVec]
  simp [dotProduct, cvec, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Cauchy–Schwarz for a symmetric positive semidefinite real bilinear form. -/
private theorem opb_cs {p : Type*} [Fintype p] (P : Matrix p p ℝ) (hP : Pᵀ = P)
    (hpos : ∀ x, 0 ≤ x ⬝ᵥ P *ᵥ x) (x y : p → ℝ) :
    |x ⬝ᵥ P *ᵥ y| ≤ Real.sqrt (x ⬝ᵥ P *ᵥ x) * Real.sqrt (y ⬝ᵥ P *ᵥ y) := by
  have hsym : y ⬝ᵥ P *ᵥ x = x ⬝ᵥ P *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]
  have hq : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ P *ᵥ y) * (t * t) + (2 * (x ⬝ᵥ P *ᵥ y)) * t + x ⬝ᵥ P *ᵥ x := by
    intro t
    have h := hpos (x + t • y)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hsym] at h
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  rw [← Real.sqrt_mul (hpos x)]
  apply Real.abs_le_sqrt
  nlinarith

/-- A weighted Cauchy–Schwarz bound for a finite complex sum with real coefficients. -/
private theorem opb_sum_bound {ι : Type*} [Fintype ι] (f g w : ι → ℝ) (c : ι → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ k, 0 ≤ w k) (hc : ∀ k, ‖c k‖ ≤ K * w k) :
    ‖∑ k, ((f k * g k : ℝ) : ℂ) * c k‖
      ≤ K * (Real.sqrt (∑ k, w k * f k ^ 2) * Real.sqrt (∑ k, w k * g k ^ 2)) := by
  calc ‖∑ k, ((f k * g k : ℝ) : ℂ) * c k‖ ≤ ∑ k, ‖((f k * g k : ℝ) : ℂ) * c k‖ := norm_sum_le _ _
    _ ≤ ∑ k, K * ((Real.sqrt (w k) * |f k|) * (Real.sqrt (w k) * |g k|)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have e : (Real.sqrt (w k) * |f k|) * (Real.sqrt (w k) * |g k|) = w k * (|f k| * |g k|) := by
          rw [show (Real.sqrt (w k) * |f k|) * (Real.sqrt (w k) * |g k|)
            = (Real.sqrt (w k) * Real.sqrt (w k)) * (|f k| * |g k|) by ring,
            Real.mul_self_sqrt (hw k)]
        rw [e]
        have := hc k
        have h0 : 0 ≤ |f k| * |g k| := by positivity
        nlinarith
    _ = K * ∑ k, (Real.sqrt (w k) * |f k|) * (Real.sqrt (w k) * |g k|) := by
        rw [Finset.mul_sum]
    _ ≤ K * (Real.sqrt (∑ k, (Real.sqrt (w k) * |f k|) ^ 2)
          * Real.sqrt (∑ k, (Real.sqrt (w k) * |g k|) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hK
    _ = K * (Real.sqrt (∑ k, w k * f k ^ 2) * Real.sqrt (∑ k, w k * g k ^ 2)) := by
        congr 3 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;>
          rw [mul_pow, Real.sq_sqrt (hw k), sq_abs]


private theorem opb_orth (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (k l : n) :
    ∑ μ, (b k).ofLp μ * (b l).ofLp μ = if k = l then 1 else 0 := by
  have h := orthonormal_iff_ite.1 b.orthonormal k l
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← h]
  simp [dotProduct, mul_comm]

private theorem opb_parseval (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (u : n → ℝ) :
    ∑ k, (u ⬝ᵥ (b k).ofLp) ^ 2 = u ⬝ᵥ u := by
  have h := b.sum_inner_mul_inner (WithLp.toLp 2 u) (WithLp.toLp 2 u)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_comm (b k).ofLp, sq]

private theorem opb_ent_spec (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (c : n → ℂ)
    (M : Matrix n n ℂ) (hM : ∀ μ ν, M μ ν = ∑ k, (((b k).ofLp μ * (b k).ofLp ν : ℝ) : ℂ) * c k)
    (u v : n → ℝ) :
    ent M u v = ∑ k, (((u ⬝ᵥ (b k).ofLp) * (v ⬝ᵥ (b k).ofLp) : ℝ) : ℂ) * c k := by
  simp only [ent, dotProduct, mulVec, cvec, hM, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum,
    Complex.ofReal_mul]
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
  ring

private theorem opb_sq_spec (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (c : n → ℂ)
    (M : Matrix n n ℂ) (hM : ∀ μ ν, M μ ν = ∑ k, (((b k).ofLp μ * (b k).ofLp ν : ℝ) : ℂ) * c k)
    (μ ρ : n) :
    (M * M) μ ρ = ∑ k, (((b k).ofLp μ * (b k).ofLp ρ : ℝ) : ℂ) * c k ^ 2 := by
  rw [mul_apply]
  simp_rw [hM, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have e : ∀ l, ∑ ν, (((b k).ofLp μ * (b k).ofLp ν : ℝ) : ℂ) * c k
      * ((((b l).ofLp ν * (b l).ofLp ρ : ℝ) : ℂ) * c l)
      = (((b k).ofLp μ * (b l).ofLp ρ : ℝ) : ℂ) * c k * c l
        * ((∑ ν, (b k).ofLp ν * (b l).ofLp ν : ℝ) : ℂ) := by
    intro l
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    push_cast; ring
  simp_rw [e, opb_orth]
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp [sq]
  ring


private theorem opb_quad_blocks (A : Matrix m m ℝ) (B : Matrix n n ℝ) (x y : m ⊕ n → ℝ) :
    x ⬝ᵥ fromBlocks A 0 0 B *ᵥ y = (x ∘ inl) ⬝ᵥ A *ᵥ (y ∘ inl) + (x ∘ inr) ⬝ᵥ B *ᵥ (y ∘ inr) := by
  simp [dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type]

private theorem opb_dot_sum (x y : m ⊕ n → ℝ) :
    x ⬝ᵥ y = (x ∘ inl) ⬝ᵥ (y ∘ inl) + (x ∘ inr) ⬝ᵥ (y ∘ inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

private theorem opb_self_nonneg {p : Type*} [Fintype p] (x : p → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

private theorem opb_Sig_nonneg {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (x : m → ℝ) :
    0 ≤ x ⬝ᵥ Sig *ᵥ x := by
  simpa using hSig.posSemidef.dotProduct_mulVec_nonneg x

private theorem opb_Sig_symm {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) : Sigᵀ = Sig := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq

private theorem opb_SigU_symm {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) :
    (SigU (n := n) Sig)ᵀ = SigU (n := n) Sig := by
  rw [SigU, fromBlocks_transpose, opb_Sig_symm hSig]
  simp

private theorem opb_SigU_nonneg {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (x : m ⊕ n → ℝ) :
    0 ≤ x ⬝ᵥ SigU (n := n) Sig *ᵥ x := by
  rw [SigU, opb_quad_blocks, one_mulVec]
  exact add_nonneg (opb_Sig_nonneg hSig _) (opb_self_nonneg _)

private theorem opb_eig_nonneg {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) (k : n) :
    0 ≤ (XSX_isHermitian hSig.1 X).eigenvalues k := by
  have h : (Xᵀ * Sig * X).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hSig.posSemidef.conjTranspose_mul_mul_same X
  exact h.eigenvalues_nonneg k

private theorem opb_JSJ (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) :
    (Jmat X)ᵀ * SigU (n := n) Sig * Jmat X = Xᵀ * Sig * X + 1 := by
  rw [Jmat, SigU, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp

/-- Bessel's inequality for the `Σ̲`-orthogonal family `J ζ_k`, `⟨J ζ_k, Σ̲ J ζ_k⟩ = 1 + λ_k`. -/
private theorem opb_bessel {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ)
    (a : m ⊕ n → ℝ) :
    ∑ k, (1 + (XSX_isHermitian hSig.1 X).eigenvalues k)⁻¹
      * (((SigU (n := n) Sig * Jmat X)ᵀ *ᵥ a) ⬝ᵥ ((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp) ^ 2
      ≤ a ⬝ᵥ SigU (n := n) Sig *ᵥ a := by
  set hA := XSX_isHermitian hSig.1 X
  set S := SigU (n := n) Sig with hSdef
  set J := Jmat X with hJdef
  set e : n → n → ℝ := fun k => (hA.eigenvectorBasis k).ofLp with he
  set lam := hA.eigenvalues
  have hlam : ∀ k, 0 < 1 + lam k := fun k => by
    have := opb_eig_nonneg hSig X k; linarith
  set α : n → ℝ := fun k => ((S * J)ᵀ *ᵥ a) ⬝ᵥ e k with hαdef
  have hS : Sᵀ = S := opb_SigU_symm hSig
  have hα : ∀ k, a ⬝ᵥ S *ᵥ (J *ᵥ e k) = α k := by
    intro k
    simp only [hαdef]
    rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec]
  have hw : ∀ k l, (J *ᵥ e k) ⬝ᵥ S *ᵥ (J *ᵥ e l) = if k = l then 1 + lam k else 0 := by
    intro k l
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, mulVec_mulVec,
      mulVec_mulVec, hSdef, hJdef, opb_JSJ, add_mulVec, one_mulVec,
      hA.mulVec_eigenvectorBasis l, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have ho := opb_orth hA.eigenvectorBasis k l
    simp only [he]
    rw [show (hA.eigenvectorBasis k).ofLp ⬝ᵥ (hA.eigenvectorBasis l).ofLp
      = ∑ μ, (hA.eigenvectorBasis k).ofLp μ * (hA.eigenvectorBasis l).ofLp μ from rfl, ho]
    by_cases hkl : k = l
    · subst hkl; simp; ring
    · simp [hkl]
  set c : n → ℝ := fun k => α k / (1 + lam k) with hc
  set v : m ⊕ n → ℝ := ∑ k, c k • (J *ᵥ e k) with hv
  have hav : a ⬝ᵥ S *ᵥ v = ∑ k, c k * α k := by
    rw [hv, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_smul, dotProduct_smul, hα, smul_eq_mul]
  have hva : v ⬝ᵥ S *ᵥ a = a ⬝ᵥ S *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]
  have hvv : v ⬝ᵥ S *ᵥ v = ∑ k, c k ^ 2 * (1 + lam k) := by
    rw [hv, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_dotProduct, mulVec_smul, Finset.sum_eq_single l]
    · rw [smul_dotProduct, dotProduct_smul, hw]; simp; ring
    · intro k _ hkl
      rw [smul_dotProduct, dotProduct_smul, hw]; simp [hkl]
    · simp
  have hpos := opb_SigU_nonneg (n := n) hSig (a - v)
  rw [← hSdef, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    hva, hav, hvv] at hpos
  have hsum : ∑ k, (1 + lam k)⁻¹ * α k ^ 2 = ∑ k, c k * α k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc]; field_simp
  have hsum2 : ∑ k, c k ^ 2 * (1 + lam k) = ∑ k, c k * α k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc]; field_simp [(hlam k).ne']
  change ∑ k, (1 + lam k)⁻¹ * α k ^ 2 ≤ _
  rw [hsum]
  linarith


private theorem opb_norm_one_le : ‖(1 : Matrix n n ℝ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (1 : Matrix n n ℝ)
  rw [conjTranspose_one, Matrix.one_mul] at h
  nlinarith [norm_nonneg (1 : Matrix n n ℝ)]

private theorem opb_euclid_sq {p : Type*} [Fintype p] (x : p → ℝ) :
    ‖(EuclideanSpace.equiv p ℝ).symm x‖ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [dotProduct, sq]

/-- `|Jᵀ a|² ≤ ‖J‖² |a|²` with `‖J‖² = ‖XᵀX + 1‖ ≤ 1 + ‖XᵀX‖`. -/
private theorem opb_Jt_bound (X : Matrix m n ℝ) (a : m ⊕ n → ℝ) :
    ((Jmat X)ᵀ *ᵥ a) ⬝ᵥ ((Jmat X)ᵀ *ᵥ a) ≤ (1 + ‖Xᵀ * X‖) * (a ⬝ᵥ a) := by
  have h1 := l2_opNorm_mulVec (Jmat X)ᵀ ((EuclideanSpace.equiv (m ⊕ n) ℝ).symm a)
  have hJ : ‖(Jmat X)ᵀ‖ ^ 2 ≤ 1 + ‖Xᵀ * X‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose, sq,
      ← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial, Jmat,
      transpose_fromRows, fromCols_mul_fromRows, transpose_one, Matrix.one_mul]
    have := opb_norm_one_le (n := n)
    have := norm_add_le (Xᵀ * X) (1 : Matrix n n ℝ)
    linarith
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, opb_euclid_sq, opb_euclid_sq] at h2
  have := opb_self_nonneg a
  calc _ ≤ ‖(Jmat X)ᵀ‖ ^ 2 * (a ⬝ᵥ a) := h2
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ this

private theorem opb_cplx_mul {p q r : Type*} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q r ℝ) :
    cplx (A * B) = cplx A * cplx B :=
  Matrix.map_mul (f := algebraMap ℝ ℂ)

private theorem opb_cplx_one {p : Type*} [DecidableEq p] : cplx (1 : Matrix p p ℝ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

private theorem opb_PN : (PN : Matrix (m ⊕ n) (m ⊕ n) ℂ) = cplx (fromBlocks 0 0 0 1) := by
  rw [PN, cplx, fromBlocks_map]
  simp

private theorem opb_SigU_inv {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) :
    SigU (n := n) Sig * (SigU (n := n) Sig)⁻¹ = 1 ∧ (SigU (n := n) Sig)⁻¹ * SigU (n := n) Sig = 1 := by
  have hd : IsUnit (SigU (n := n) Sig).det := by
    rw [SigU, det_fromBlocks_zero₂₁, det_one, mul_one]
    exact (isUnit_iff_isUnit_det _).1 hSig.isUnit
  exact ⟨mul_nonsing_inv _ hd, nonsing_inv_mul _ hd⟩

/-- `Σ̲ − (Σ ⊕ 0) = P_N`, `Σ̲ P_N = P_N`, `P_N Σ̲ = P_N`, `(Σ ⊕ 0) P_N = P_N (Σ ⊕ 0) = 0`,
`Jᵀ P_N J = 1`. -/
private theorem opb_blocks (Sig : Matrix m m ℝ) (X : Matrix m n ℝ) :
    SigU (n := n) Sig - fromBlocks Sig 0 0 0
      = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) ∧
    SigU (n := n) Sig * fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ)
      = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) ∧
    fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) * SigU (n := n) Sig
      = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) ∧
    fromBlocks Sig 0 0 (0 : Matrix n n ℝ) * fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ)
      = 0 ∧
    fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) * fromBlocks Sig 0 0 (0 : Matrix n n ℝ)
      = 0 ∧
    (Jmat X)ᵀ * fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) * Jmat X = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SigU, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]; simp
  · rw [SigU, fromBlocks_multiply]; simp
  · rw [SigU, fromBlocks_multiply]; simp
  · rw [fromBlocks_multiply]; simp
  · rw [fromBlocks_multiply]; simp
  · rw [Jmat, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]; simp

private theorem opb_cplx_SigU_inv {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) :
    cplx (SigU (n := n) Sig) * cplx (SigU (n := n) Sig)⁻¹ = 1 ∧
    cplx (SigU (n := n) Sig)⁻¹ * cplx (SigU (n := n) Sig) = 1 := by
  obtain ⟨h1, h2⟩ := opb_SigU_inv (n := n) hSig
  rw [← opb_cplx_mul, ← opb_cplx_mul, h1, h2, opb_cplx_one]
  exact ⟨rfl, rfl⟩

/-- From (decompfullG): `Σ̲⁻¹ (G + Σ̲) Σ̲⁻¹ = P_N + J G_N Jᵀ`. -/
private theorem opb_ident_G {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    cplx (SigU (n := n) Sig)⁻¹ * (G Sig X z + cplx (SigU (n := n) Sig)) * cplx (SigU (n := n) Sig)⁻¹
      = PN + cplx (Jmat X) * GN Sig X z * cplx (Jmat X)ᵀ := by
  obtain ⟨hS1, hS2⟩ := opb_cplx_SigU_inv (n := n) hSig
  obtain ⟨b1, b2, b3, -, -, -⟩ := opb_blocks (n := n) Sig X
  have hSi : (SigU (n := n) Sig)⁻¹ * fromBlocks 0 0 0 1 * (SigU (n := n) Sig)⁻¹
      = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) := by
    obtain ⟨r1, r2⟩ := opb_SigU_inv (n := n) hSig
    have e1 : (SigU (n := n) Sig)⁻¹ * fromBlocks 0 0 0 1
        = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) := by
      calc (SigU (n := n) Sig)⁻¹ * fromBlocks 0 0 0 1
          = (SigU (n := n) Sig)⁻¹ * (SigU (n := n) Sig * fromBlocks 0 0 0 1) := by rw [b2]
        _ = _ := by rw [← Matrix.mul_assoc, r2, Matrix.one_mul]
    rw [e1]
    calc fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) * (SigU (n := n) Sig)⁻¹
        = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) * SigU (n := n) Sig
          * (SigU (n := n) Sig)⁻¹ := by rw [b3]
      _ = _ := by rw [Matrix.mul_assoc, r1, Matrix.mul_one]
  have hPN : cplx (SigU (n := n) Sig) - cplx (fromBlocks Sig 0 0 (0 : Matrix n n ℝ)) = PN := by
    rw [opb_PN, ← b1]; ext i j; simp [cplx]
  have hG : G Sig X z + cplx (SigU (n := n) Sig) = PN + cplx (SigU (n := n) Sig)
      * (cplx (Jmat X) * GN Sig X z * cplx (Jmat X)ᵀ) * cplx (SigU (n := n) Sig) := by
    rw [decompfullG hSig X hz, ← hPN]
    simp only [Matrix.mul_assoc]
    abel
  rw [hG, Matrix.mul_add, Matrix.add_mul]
  congr 1
  · rw [opb_PN, ← opb_cplx_mul, ← opb_cplx_mul, hSi]
  · simp only [← Matrix.mul_assoc]
    rw [hS2, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hS1, Matrix.mul_one]

/-- From (decompfullG): `G P_N G = Σ̲ J G_N² Jᵀ Σ̲`. -/
private theorem opb_ident_GPG {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    G Sig X z * (PN : Matrix (m ⊕ n) (m ⊕ n) ℂ) * G Sig X z
      = cplx (SigU (n := n) Sig) * cplx (Jmat X) * (GN Sig X z * GN Sig X z) * cplx (Jmat X)ᵀ
        * cplx (SigU (n := n) Sig) := by
  obtain ⟨-, b2, b3, b4, b5, b6⟩ := opb_blocks (n := n) Sig X
  have hDP : cplx (fromBlocks Sig 0 0 (0 : Matrix n n ℝ)) * PN = 0 := by
    rw [opb_PN, ← opb_cplx_mul, b4]; simp [cplx]
  have hPD : PN * cplx (fromBlocks Sig 0 0 (0 : Matrix n n ℝ)) = 0 := by
    rw [opb_PN, ← opb_cplx_mul, b5]; simp [cplx]
  have hcore : cplx (Jmat X)ᵀ * cplx (SigU (n := n) Sig) * (PN : Matrix (m ⊕ n) (m ⊕ n) ℂ)
      * cplx (SigU (n := n) Sig) * cplx (Jmat X) = (1 : Matrix n n ℂ) := by
    rw [opb_PN, ← opb_cplx_mul, ← opb_cplx_mul, ← opb_cplx_mul, ← opb_cplx_mul,
      Matrix.mul_assoc ((Jmat X)ᵀ), b2, Matrix.mul_assoc ((Jmat X)ᵀ), b3, b6, opb_cplx_one]
  rw [decompfullG hSig X hz]
  set Q := cplx (SigU (n := n) Sig) * cplx (Jmat X) * GN Sig X z * cplx (Jmat X)ᵀ
    * cplx (SigU (n := n) Sig) with hQ
  have h1 : (-cplx (fromBlocks Sig 0 0 (0 : Matrix n n ℝ)) + Q) * PN = Q * PN := by
    rw [Matrix.add_mul, Matrix.neg_mul, hDP, neg_zero, zero_add]
  rw [h1, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_assoc Q PN, hPD, Matrix.mul_zero, neg_zero,
    zero_add]
  have hcore' : ∀ Y : Matrix n (m ⊕ n) ℂ, cplx (Jmat X)ᵀ * (cplx (SigU (n := n) Sig)
      * ((PN : Matrix (m ⊕ n) (m ⊕ n) ℂ) * (cplx (SigU (n := n) Sig) * (cplx (Jmat X) * Y)))) = Y := by
    intro Y
    simp only [← Matrix.mul_assoc]
    rw [hcore, Matrix.one_mul]
  simp only [hQ, Matrix.mul_assoc]
  rw [hcore']

private theorem opb_RR {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ)
    (M : Matrix n n ℂ) :
    cplx (SigU (n := n) Sig) * cplx (Jmat X) * M * cplx (Jmat X)ᵀ * cplx (SigU (n := n) Sig)
      = cplx (SigU (n := n) Sig * Jmat X) * M * cplx (SigU (n := n) Sig * Jmat X)ᵀ := by
  rw [transpose_mul, opb_SigU_symm hSig, opb_cplx_mul, opb_cplx_mul]
  simp only [Matrix.mul_assoc]


/-- `(Σ ⊕ 0)` is a symmetric positive semidefinite form dominated by `Σ̲`. -/
private theorem opb_D_props {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) :
    (fromBlocks Sig 0 0 (0 : Matrix n n ℝ))ᵀ = fromBlocks Sig 0 0 (0 : Matrix n n ℝ) ∧
    (∀ x, 0 ≤ x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix n n ℝ) *ᵥ x) ∧
    (∀ x, x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix n n ℝ) *ᵥ x ≤ x ⬝ᵥ SigU (n := n) Sig *ᵥ x) := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · rw [fromBlocks_transpose, opb_Sig_symm hSig]; simp
  · rw [opb_quad_blocks]; simpa using opb_Sig_nonneg hSig (x ∘ inl)
  · rw [opb_quad_blocks, SigU, opb_quad_blocks]
    simpa using opb_self_nonneg (x ∘ inr)

/-- `P_N = 0 ⊕ 1` is a symmetric positive semidefinite form dominated by the identity. -/
private theorem opb_P_props :
    (fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ))ᵀ
      = fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) ∧
    (∀ x, 0 ≤ x ⬝ᵥ fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) *ᵥ x) ∧
    (∀ x, x ⬝ᵥ fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) *ᵥ x ≤ x ⬝ᵥ x) := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · rw [fromBlocks_transpose]; simp
  · rw [opb_quad_blocks]; simpa using opb_self_nonneg (x ∘ inr)
  · rw [opb_quad_blocks, opb_dot_sum]
    simpa using opb_self_nonneg (x ∘ inl)

/-- For real `λ` and `Im z > 0`: `η ≤ |λ - z|`, `η ≤ |z|`, `λ ≤ |λ - z| + |z|`. -/
private theorem opb_lam_bounds (lam : ℝ) {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ ‖(lam : ℂ) - z‖ ∧ z.im ≤ ‖z‖ ∧ lam ≤ ‖(lam : ℂ) - z‖ + ‖z‖ := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Complex.abs_im_le_norm ((lam : ℂ) - z)
    rwa [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at h
  · have h := Complex.abs_im_le_norm z
    rwa [abs_of_pos hz] at h
  · have h := norm_sub_norm_le (lam : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    linarith [le_abs_self lam]

private theorem opb_inv_le {d w K : ℝ} (hd : 0 < d) (hw : 0 < w) (h : w ≤ K * d) :
    d⁻¹ ≤ K * w⁻¹ := by
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hd hw]
  linarith

/-- `|λ - z|⁻¹ ≤ ((1 + 5|z|)/η - 1) (1 + λ)⁻¹` for `λ ≥ 0`. -/
private theorem opb_const1 {lam : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 < z.im) :
    ‖((lam : ℂ) - z)⁻¹‖ ≤ ((1 + 5 * ‖z‖) / z.im - 1) * (1 + lam)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := opb_lam_bounds lam hz
  have hd : 0 < ‖(lam : ℂ) - z‖ := lt_of_lt_of_le hz h1
  rw [norm_inv]
  refine opb_inv_le hd (by linarith) ?_
  rw [div_sub_one hz.ne', div_mul_eq_mul_div, le_div_iff₀ hz]
  have e1 := mul_le_mul_of_nonneg_right h2 hd.le
  have e2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg z)
  have e3 := mul_le_mul_of_nonneg_left h3 hz.le
  have e4 := mul_nonneg (norm_nonneg z) hd.le
  nlinarith

/-- (GN_spec) with `1/(λ_k - z)` written as `(λ_k - z)⁻¹`. -/
private theorem opb_GN_entries {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (μ ν : n) :
    GN Sig X z μ ν = ∑ k, ((((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp μ
        * ((XSX_isHermitian hSig.1 X).eigenvectorBasis k).ofLp ν : ℝ) : ℂ)
        * (((XSX_isHermitian hSig.1 X).eigenvalues k : ℂ) - z)⁻¹ := by
  rw [GN_spec hSig X hz]
  simp only [div_eq_mul_inv]

/-- `|⟨u, G_N v⟩| ≤ η⁻¹ |u| |v|` and `|⟨u, G_N² v⟩| ≤ η⁻² |u| |v|` for real `u`, `v`. -/
private theorem opb_GN_bound {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ}
    (hz : 0 < z.im) (u v : n → ℝ) :
    ‖ent (GN Sig X z) u v‖ ≤ 1 / z.im * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) ∧
    ‖ent (GN Sig X z * GN Sig X z) u v‖
      ≤ 1 / z.im ^ 2 * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
  set hA := XSX_isHermitian hSig.1 X
  have hP : ∀ x : n → ℝ, ∑ k, (1 : ℝ) * (x ⬝ᵥ (hA.eigenvectorBasis k).ofLp) ^ 2 = x ⬝ᵥ x := by
    intro x; simp only [one_mul]; exact opb_parseval hA.eigenvectorBasis x
  have hd : ∀ k, z.im ≤ ‖(hA.eigenvalues k : ℂ) - z‖ := fun k => (opb_lam_bounds _ hz).1
  refine ⟨?_, ?_⟩
  · rw [opb_ent_spec hA.eigenvectorBasis _ _ (opb_GN_entries hSig X hz) u v, ← hP u, ← hP v]
    refine opb_sum_bound _ _ _ _ _ (by positivity) (fun _ => zero_le_one) fun k => ?_
    rw [norm_inv, mul_one, one_div]
    exact inv_anti₀ hz (hd k)
  · rw [opb_ent_spec hA.eigenvectorBasis _ _ (opb_sq_spec hA.eigenvectorBasis _ _
      (opb_GN_entries hSig X hz)) u v, ← hP u, ← hP v]
    refine opb_sum_bound _ _ _ _ _ (by positivity) (fun _ => zero_le_one) fun k => ?_
    rw [norm_pow, norm_inv, mul_one, one_div, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hz.le (hd k) 2)

/-- `|Jᵀ a| ≤ (1 + ‖XᵀX‖)^{1/2} |a|`. -/
private theorem opb_sqrt_J (X : Matrix m n ℝ) (a : m ⊕ n → ℝ) :
    Real.sqrt (((Jmat X)ᵀ *ᵥ a) ⬝ᵥ ((Jmat X)ᵀ *ᵥ a))
      ≤ Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (a ⬝ᵥ a) := by
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (opb_Jt_bound X a)

section L46
variable {Sig : Matrix m m ℝ} (hSig : Sig.PosDef) (X : Matrix m n ℝ) {z : ℂ} (hz : 0 < z.im)
include hSig hz

/-- (opbound), first bound, weighted bilinear form (`a = Σ̲^{-1/2} x`). -/
theorem opbound (a b : m ⊕ n → ℝ) :
    ‖ent (G Sig X z) a b‖ ≤ (1 + 5 * ‖z‖) / z.im
      * Real.sqrt (a ⬝ᵥ SigU (n := n) Sig *ᵥ a) * Real.sqrt (b ⬝ᵥ SigU (n := n) Sig *ᵥ b) := by
  set hA := XSX_isHermitian hSig.1 X
  set R := SigU (n := n) Sig * Jmat X
  obtain ⟨hDs, hDn, hDle⟩ := opb_D_props (n := n) hSig
  have hent : ent (G Sig X z) a b
      = -((a ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix n n ℝ) *ᵥ b : ℝ) : ℂ)
        + ∑ k, ((((Rᵀ *ᵥ a) ⬝ᵥ (hA.eigenvectorBasis k).ofLp)
          * ((Rᵀ *ᵥ b) ⬝ᵥ (hA.eigenvectorBasis k).ofLp) : ℝ) : ℂ)
          * ((hA.eigenvalues k : ℂ) - z)⁻¹ := by
    rw [decompfullG hSig X hz, opb_ent_add, opb_ent_neg, opb_ent_cplx, opb_RR hSig, opb_ent_congr,
      opb_ent_spec hA.eigenvectorBasis _ _ (opb_GN_entries hSig X hz)]
  have hK : 0 ≤ (1 + 5 * ‖z‖) / z.im - 1 := by
    have := (opb_lam_bounds 0 hz).2.1
    rw [div_sub_one hz.ne']
    exact div_nonneg (by linarith [norm_nonneg z]) hz.le
  have hsum := opb_sum_bound (fun k => (Rᵀ *ᵥ a) ⬝ᵥ (hA.eigenvectorBasis k).ofLp)
    (fun k => (Rᵀ *ᵥ b) ⬝ᵥ (hA.eigenvectorBasis k).ofLp) (fun k => (1 + hA.eigenvalues k)⁻¹)
    (fun k => ((hA.eigenvalues k : ℂ) - z)⁻¹) _ hK
    (fun k => inv_nonneg.2 (by linarith [opb_eig_nonneg hSig X k]))
    (fun k => opb_const1 (opb_eig_nonneg hSig X k) hz)
  have hBa := Real.sqrt_le_sqrt (opb_bessel hSig X a)
  have hBb := Real.sqrt_le_sqrt (opb_bessel hSig X b)
  have hcs := opb_cs _ hDs hDn a b
  have hca := Real.sqrt_le_sqrt (hDle a)
  have hcb := Real.sqrt_le_sqrt (hDle b)
  set qa := Real.sqrt (a ⬝ᵥ SigU (n := n) Sig *ᵥ a)
  set qb := Real.sqrt (b ⬝ᵥ SigU (n := n) Sig *ᵥ b)
  have hqa : 0 ≤ qa := Real.sqrt_nonneg _
  have hqb : 0 ≤ qb := Real.sqrt_nonneg _
  rw [hent]
  calc _ ≤ ‖-((a ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix n n ℝ) *ᵥ b : ℝ) : ℂ)‖
        + ‖∑ k, ((((Rᵀ *ᵥ a) ⬝ᵥ (hA.eigenvectorBasis k).ofLp)
          * ((Rᵀ *ᵥ b) ⬝ᵥ (hA.eigenvectorBasis k).ofLp) : ℝ) : ℂ)
          * ((hA.eigenvalues k : ℂ) - z)⁻¹‖ := norm_add_le _ _
    _ ≤ qa * qb + ((1 + 5 * ‖z‖) / z.im - 1) * (qa * qb) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
        refine add_le_add (hcs.trans (mul_le_mul hca hcb (Real.sqrt_nonneg _) hqa)) ?_
        refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hK)
        exact mul_le_mul hBa hBb (Real.sqrt_nonneg _) hqa
    _ = _ := by ring

/-- Lemma 4.9, first bound, with the explicit constant `(1 + ‖XᵀX‖)/η + 1`. -/
theorem opnorm_G (a b : m ⊕ n → ℝ) :
    ‖ent (cplx (SigU (n := n) Sig)⁻¹ * (G Sig X z + cplx (SigU (n := n) Sig)) * cplx (SigU (n := n) Sig)⁻¹) a b‖
      ≤ ((1 + ‖Xᵀ * X‖) / z.im + 1) * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
  obtain ⟨hPs, hPn, hPle⟩ := opb_P_props (m := m) (n := n)
  rw [opb_ident_G hSig X hz, opb_ent_add, opb_PN, opb_ent_cplx, opb_ent_congr]
  have h1 := (opb_cs _ hPs hPn a b).trans (mul_le_mul (Real.sqrt_le_sqrt (hPle a))
    (Real.sqrt_le_sqrt (hPle b)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h2 := (opb_GN_bound hSig X hz ((Jmat X)ᵀ *ᵥ a) ((Jmat X)ᵀ *ᵥ b)).1
  have hJ := mul_le_mul (opb_sqrt_J X a) (opb_sqrt_J X b) (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hN : Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (1 + ‖Xᵀ * X‖) = 1 + ‖Xᵀ * X‖ :=
    Real.mul_self_sqrt (by positivity)
  have hη : 0 ≤ 1 / z.im := by positivity
  calc _ ≤ ‖(((a ⬝ᵥ fromBlocks (0 : Matrix m m ℝ) 0 0 (1 : Matrix n n ℝ) *ᵥ b) : ℝ) : ℂ)‖
        + ‖ent (GN Sig X z) ((Jmat X)ᵀ *ᵥ a) ((Jmat X)ᵀ *ᵥ b)‖ := norm_add_le _ _
    _ ≤ Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) + 1 / z.im
        * ((Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (a ⬝ᵥ a))
          * (Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (b ⬝ᵥ b))) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hJ hη))
    _ = _ := by
        rw [show Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (a ⬝ᵥ a)
            * (Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (b ⬝ᵥ b))
          = (Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (1 + ‖Xᵀ * X‖))
            * (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b)) by ring, hN]
        ring

/-- Lemma 4.9, second bound, with the explicit constant `(1 + ‖XᵀX‖)/η²`. -/
theorem opnorm_dG (a b : m ⊕ n → ℝ) :
    ‖ent (cplx (SigU (n := n) Sig)⁻¹ * (G Sig X z * (PN : Matrix (m ⊕ n) (m ⊕ n) ℂ) * G Sig X z) * cplx (SigU (n := n) Sig)⁻¹) a b‖
      ≤ (1 + ‖Xᵀ * X‖) / z.im ^ 2 * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
  obtain ⟨hS1, hS2⟩ := opb_cplx_SigU_inv (n := n) hSig
  have e : cplx (SigU (n := n) Sig)⁻¹ * (G Sig X z * (PN : Matrix (m ⊕ n) (m ⊕ n) ℂ) * G Sig X z)
      * cplx (SigU (n := n) Sig)⁻¹
      = cplx (Jmat X) * (GN Sig X z * GN Sig X z) * cplx (Jmat X)ᵀ := by
    rw [opb_ident_GPG hSig X hz]
    simp only [← Matrix.mul_assoc]
    rw [hS2, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hS1, Matrix.mul_one]
  rw [e, opb_ent_congr]
  have h2 := (opb_GN_bound hSig X hz ((Jmat X)ᵀ *ᵥ a) ((Jmat X)ᵀ *ᵥ b)).2
  have hJ := mul_le_mul (opb_sqrt_J X a) (opb_sqrt_J X b) (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hN : Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (1 + ‖Xᵀ * X‖) = 1 + ‖Xᵀ * X‖ :=
    Real.mul_self_sqrt (by positivity)
  have hη : 0 ≤ 1 / z.im ^ 2 := by positivity
  refine (h2.trans (mul_le_mul_of_nonneg_left hJ hη)).trans_eq ?_
  rw [show Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (a ⬝ᵥ a)
      * (Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (b ⬝ᵥ b))
    = (Real.sqrt (1 + ‖Xᵀ * X‖) * Real.sqrt (1 + ‖Xᵀ * X‖))
      * (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b)) by ring, hN]
  ring

end L46

end Anisotropic

#print axioms Anisotropic.opbound
#print axioms Anisotropic.opnorm_G
#print axioms Anisotropic.opnorm_dG
