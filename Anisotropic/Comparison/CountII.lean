module

public import Anisotropic.Comparison.ColumnMoment
public import Anisotropic.Comparison.WordBounds
public import Anisotropic.Framework.DominationMoment

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The family `𝒱_v`, `max_{𝒱_v} E F^p`, and Lemma 8.8: the tagged-word sum (sec8 2) -/

/-- `𝒱_v = {v} ∪ {e_μ : μ ∈ 𝓘_N}`, indexed by `Option (Fin N)` (Section 8, after Lemma 8.2). -/
def vfam (v : Fin M ⊕ Fin N → ℝ) : Option (Fin N) → (Fin M ⊕ Fin N → ℝ)
  | none => v
  | some μ => eI (Sum.inr μ)

/-- `𝒱_w ⊆ 𝒱_v` for every `w ∈ 𝒱_v`. -/
theorem vfam_closed (v : Fin M ⊕ Fin N → ℝ) (w u : Option (Fin N)) :
    ∃ u' : Option (Fin N), vfam (vfam v w) u = vfam v u' := by
  cases u with
  | none => exact ⟨w, rfl⟩
  | some μ => exact ⟨some μ, rfl⟩

/-- `max_{w ∈ 𝒱_v} E F_w^p(X)`. -/
def maxFp {Ω : Type*} [MeasureSpace Ω] (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (p : ℕ) : ℝ :=
  ⨆ w : Option (Fin N), ∫ ω, Fv Sig (X ω) z (vfam v w) ^ p

/-! ## Elementary estimates -/

section Elementary

private theorem cII_conjIf_mul (b : Bool) (x y : ℂ) :
    conjIf b (x * y) = conjIf b x * conjIf b y := by
  cases b <;> simp [conjIf]

private theorem cII_conjIf_pow (b : Bool) (x : ℂ) (n : ℕ) : conjIf b (x ^ n) = conjIf b x ^ n := by
  cases b <;> simp [conjIf]

private theorem cII_norm_conjIf (b : Bool) (x : ℂ) : ‖conjIf b x‖ = ‖x‖ := by
  cases b <;> simp [conjIf]

private theorem cII_conjIf_sum {ι : Type*} (s : Finset ι) (b : Bool) (f : ι → ℂ) :
    conjIf b (∑ i ∈ s, f i) = ∑ i ∈ s, conjIf b (f i) := by
  cases b <;> simp [conjIf, map_sum]

private theorem cII_continuous_conjIf (b : Bool) : Continuous (conjIf b) := by
  cases b
  · have h : conjIf false = id := funext fun x => by simp [conjIf]
    rw [h]; exact continuous_id
  · have h : conjIf true = starRingEnd ℂ := funext fun x => by simp [conjIf]
    rw [h]; exact Complex.continuous_conj

/-- `|x^n − y^n| ≤ n L^{n−1} |x − y|` for `|x|, |y| ≤ L`. -/
private theorem cII_pow_sub_le {x y : ℂ} {L : ℝ} (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * L ^ (n - 1) * ‖x - y‖ := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hx
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖x‖ * ‖x ^ n - y ^ n‖ ≤ L * (n * L ^ (n - 1) * ‖x - y‖) :=
      mul_le_mul hx ih (norm_nonneg _) hL
    have h2 : ‖x - y‖ * ‖y‖ ^ n ≤ ‖x - y‖ * L ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy n) (norm_nonneg _)
    rcases n with _ | n
    · simp only [Nat.cast_zero, zero_mul, mul_zero, pow_zero, mul_one] at h1 h2 ⊢
      norm_num
    · have e2 : L * ((n + 1 : ℕ) * L ^ (n + 1 - 1) * ‖x - y‖) =
          (n + 1 : ℕ) * L ^ (n + 1) * ‖x - y‖ := by
        simp only [Nat.add_sub_cancel, pow_succ]; ring
      rw [e2] at h1
      simp only [Nat.add_sub_cancel]
      push_cast at h1 ⊢
      nlinarith

/-- `|∏ X − ∏ Y| ≤ (∑ θ) ∏ m` when `|X_i|, |Y_i| ≤ m_i` and `|X_i − Y_i| ≤ θ_i m_i`. -/
private theorem cII_prod_sub_le {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) (m θ : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hX : ∀ i ∈ s, ‖X i‖ ≤ m i) (hY : ∀ i ∈ s, ‖Y i‖ ≤ m i)
    (hXY : ∀ i ∈ s, ‖X i - Y i‖ ≤ θ i * m i) :
    ‖∏ i ∈ s, X i - ∏ i ∈ s, Y i‖ ≤ (∑ i ∈ s, θ i) * ∏ i ∈ s, m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hm hX hY hXY
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have hYs : ‖∏ i ∈ s, Y i‖ ≤ ∏ i ∈ s, m i :=
      (Finset.norm_prod_le s Y).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hY.2)
    have hms : 0 ≤ ∏ i ∈ s, m i := Finset.prod_nonneg hm.2
    have e : X a * ∏ i ∈ s, X i - Y a * ∏ i ∈ s, Y i =
        X a * (∏ i ∈ s, X i - ∏ i ∈ s, Y i) + (X a - Y a) * ∏ i ∈ s, Y i := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hX.1 (ih hm.2 hX.2 hY.2 hXY.2) (norm_nonneg _) hm.1
    have h2 := mul_le_mul hXY.1 hYs (norm_nonneg _) (by
      have := norm_nonneg (X a - Y a); linarith [hXY.1])
    nlinarith

end Elementary

/-! ## Deterministic bounds on the entries of `G`, `G^{(μ)}` -/

section Entries

private theorem cII_ent_eq {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem cII_ent_eI_right {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (x : ι → ℝ) (r : ι) : ent B x (eI r) = ∑ s, (x s : ℂ) * B s r := by
  rw [cII_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [eI, Pi.single_apply, apply_ite]

private theorem cII_ent_eI_left {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (y : ι → ℝ) (r : ι) : ent B (eI r) y = ∑ t, B r t * (y t : ℂ) := by
  rw [cII_ent_eq]
  simp [eI, Pi.single_apply, apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem cII_ent_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A + B) v w = ent A v w + ent B v w := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem cII_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem cII_ent_cplx {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ) :
    ent (cplx A) v w = ((v ⬝ᵥ A *ᵥ w : ℝ) : ℂ) := by
  simp [ent, cplx, dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The column `μ` of `X̂` vanishes for `X` with column `μ` set to `0`. -/
private theorem cII_Xhat_col (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (q : Fin M ⊕ Fin N) :
    Xhat (updCol A μ 0) q (Sum.inr μ) = 0 := by
  rcases q with j | ν
  · simp [Xhat, cplx, updCol]
  · simp [Xhat]

/-- `G^{(μ)} = G(X⁰) + z⁻¹ e_μ e_μ^*` for `X⁰` the matrix `X` with column `μ` set to `0`. -/
private theorem cII_Gmu_apply {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (s t : Fin M ⊕ Fin N) :
    Gmu Sig A z μ s t = G Sig (updCol A μ 0) z s t +
      (if s = Sum.inr μ ∧ t = Sum.inr μ then z⁻¹ else 0) := by
  set A0 := updCol A μ 0 with hA0
  have hcol : ∀ x : Fin M ⊕ Fin N → ℝ,
      ent (G1 Sig A0 z (Sum.inr μ) * Xhat A0) x (eI (Sum.inr μ)) = 0 := by
    intro x
    rw [cII_ent_eI_right]
    refine Finset.sum_eq_zero fun r _ => ?_
    simp [Matrix.mul_apply, hA0, cII_Xhat_col]
  have hrow : ∀ y : Fin M ⊕ Fin N → ℝ,
      ent ((Xhat A0)ᵀ * G1 Sig A0 z (Sum.inr μ)) (eI (Sum.inr μ)) y = 0 := by
    intro y
    rw [cII_ent_eI_left]
    refine Finset.sum_eq_zero fun r _ => ?_
    simp [Matrix.mul_apply, hA0, cII_Xhat_col]
  have hQ : ((Xhat A0)ᵀ * G1 Sig A0 z (Sum.inr μ) * Xhat A0) (Sum.inr μ) (Sum.inr μ) = 0 := by
    simp [Matrix.mul_apply, hA0, cII_Xhat_col]
  have hii := Gii hSig A0 hz μ
  rw [hQ, sub_zero] at hii
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl 0 hz
  have hg : G Sig A0 z (Sum.inr μ) (Sum.inr μ) = -z⁻¹ := by
    have hne := G_diag_ne_zero hSig A0 hz (Sum.inr μ)
    have : G Sig A0 z (Sum.inr μ) (Sum.inr μ) = 1 / (-z) := by
      rw [← hii, one_div_one_div]
    rw [this, one_div, inv_neg]
  have hm := main_identity hSig A0 hz μ (eI s) (eI t)
  rw [hcol, hrow, ent_eI_eI, ent_eI_eI] at hm
  have hG1 : G1 Sig A0 z (Sum.inr μ) = Gmu Sig A z μ := Gmu_updCol Sig A z μ 0
  rw [hG1, hg] at hm
  by_cases hs : s = Sum.inr μ <;> by_cases ht : t = Sum.inr μ
  · subst hs; subst ht
    simp [eI] at hm
    simp only [and_self, ite_true]
    linear_combination -hm
  · simp [eI, hs, ht] at hm
    simp [hs, ht, hm]
  · simp [eI, hs, ht] at hm
    simp [hs, ht, hm]
  · simp [eI, hs, ht] at hm
    simp [hs, ht, hm]

/-- `G^{(μ)}_{xy} = G(X⁰)_{xy} + x(μ) y(μ) z⁻¹`. -/
private theorem cII_ent_Gmu {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (Gmu Sig A z μ) x y = ent (G Sig (updCol A μ 0) z) x y +
      ((x (Sum.inr μ) : ℂ) * (y (Sum.inr μ) : ℂ)) * z⁻¹ := by
  rw [cII_ent_eq, cII_ent_eq]
  simp only [cII_Gmu_apply hSig A hz μ, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_eq_single (Sum.inr μ)]
  · rw [Finset.sum_eq_single (Sum.inr μ)]
    · simp; ring
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [hb]
  · simp

private theorem cII_cplx_SigU_inv {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    cplx (SigU (n := Fin N) Sig) * cplx (SigU (n := Fin N) Sig)⁻¹ = 1 ∧
      cplx (SigU (n := Fin N) Sig)⁻¹ * cplx (SigU (n := Fin N) Sig) = 1 := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have hS' : Sig⁻¹ * Sig = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  have h1 : SigU (n := Fin N) Sig * fromBlocks Sig⁻¹ 0 0 1 = 1 := by
    rw [SigU, fromBlocks_multiply]
    simp [hS]
  have h2 : fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ) * SigU (n := Fin N) Sig = 1 := by
    rw [SigU, fromBlocks_multiply]
    simp [hS']
  have c1 : cplx (SigU (n := Fin N) Sig) *
      cplx (fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ)) = 1 := by
    simp only [cplx]
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have c2 : cplx (fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ)) *
      cplx (SigU (n := Fin N) Sig) = 1 := by
    simp only [cplx]
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv : (SigU (n := Fin N) Sig)⁻¹ = fromBlocks Sig⁻¹ 0 0 (1 : Matrix (Fin N) (Fin N) ℝ) :=
    Matrix.inv_eq_right_inv h1
  rw [hinv]
  exact ⟨c1, c2⟩

private theorem cII_SigU_transpose {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    (SigU (n := Fin N) Sig)ᵀ = SigU (n := Fin N) Sig := by
  have hS : Sigᵀ = Sig := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hSig.1.eq
  unfold SigU
  rw [fromBlocks_transpose]
  simp [hS]

private theorem cII_cvec_mulVec {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (a : ι → ℝ) :
    cvec (Q *ᵥ a) = cplx Q *ᵥ cvec a := by
  ext s
  simp [cplx, cvec, Matrix.mulVec, dotProduct]

private theorem cII_ent_G_add_u {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (a b : Fin M ⊕ Fin N → ℝ) :
    ent (G Sig A z + cplx (SigU (n := Fin N) Sig)) a b =
      ent (cplx (SigU (n := Fin N) Sig)⁻¹ * (G Sig A z + cplx (SigU (n := Fin N) Sig)) *
        cplx (SigU (n := Fin N) Sig)⁻¹)
        (SigU (n := Fin N) Sig *ᵥ a) (SigU (n := Fin N) Sig *ᵥ b) := by
  obtain ⟨hu, hV⟩ := cII_cplx_SigU_inv (N := N) hSig
  set u := cplx (SigU (n := Fin N) Sig) with hudef
  set V := cplx (SigU (n := Fin N) Sig)⁻¹ with hVdef
  have hT : uᵀ = u := by
    rw [hudef, cplx, ← Matrix.transpose_map, cII_SigU_transpose hSig]
  have key : ∀ (S B : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℂ), Sᵀ = S →
      ∀ a b : Fin M ⊕ Fin N → ℂ, (S *ᵥ a) ⬝ᵥ (B *ᵥ (S *ᵥ b)) = a ⬝ᵥ ((S * B * S) *ᵥ b) := by
    intro S B hS a b
    rw [← vecMul_transpose, hS, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  unfold ent
  rw [cII_cvec_mulVec, cII_cvec_mulVec, key u _ hT]
  congr 2
  calc G Sig A z + u = (u * V) * (G Sig A z + u) * (V * u) := by rw [hu, hV]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem cII_dot_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ testNorm x * testNorm y := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun s => |x s|) (fun s => |y s|)
  simp only [sq_abs] at h
  unfold testNorm
  calc |x ⬝ᵥ y| = |∑ s, x s * y s| := rfl
    _ ≤ ∑ s, |x s * y s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, |x s| * |y s| := by simp [abs_mul]
    _ ≤ _ := h

private theorem cII_sqrt_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (x ⬝ᵥ x) = testNorm x := by
  unfold testNorm
  congr 1
  simp [dotProduct, sq]

private theorem cII_testNorm_eI {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι) :
    testNorm (eI s) = 1 := by
  unfold testNorm eI
  simp [Pi.single_apply]

private theorem cII_dot_SigU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (x y : Fin M ⊕ Fin N → ℝ) :
    x ⬝ᵥ SigU (n := Fin N) Sig *ᵥ y = (SigU (n := Fin N) Sig *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, cII_SigU_transpose hSig]

/-- `|G_{ab}| ≤ ((1 + ‖XᵀX‖)/η + 1) |Σ̲a| |Σ̲b| + min(|a| |Σ̲b|, |Σ̲a| |b|)` (through the bound of
`Σ̲⁻¹(G + Σ̲)Σ̲⁻¹`, Lemma 4.9). -/
private theorem cII_G_bound {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (a b : Fin M ⊕ Fin N → ℝ) :
    ‖ent (G Sig A z) a b‖ ≤
        ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ a) *
          testNorm (SigU (n := Fin N) Sig *ᵥ b) +
        min (testNorm a * testNorm (SigU (n := Fin N) Sig *ᵥ b))
          (testNorm (SigU (n := Fin N) Sig *ᵥ a) * testNorm b) := by
  have h1 := opnorm_G hSig A hz (SigU (n := Fin N) Sig *ᵥ a) (SigU (n := Fin N) Sig *ᵥ b)
  rw [cII_sqrt_dot, cII_sqrt_dot] at h1
  have h2 := cII_ent_G_add_u hSig A z a b
  rw [cII_ent_add, cII_ent_cplx] at h2
  have h3 : ent (G Sig A z) a b = ent (cplx (SigU (n := Fin N) Sig)⁻¹ *
      (G Sig A z + cplx (SigU (n := Fin N) Sig)) * cplx (SigU (n := Fin N) Sig)⁻¹)
      (SigU (n := Fin N) Sig *ᵥ a) (SigU (n := Fin N) Sig *ᵥ b) -
      ((a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b : ℝ) : ℂ) := by
    rw [← h2]; ring
  have hd1 : |a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b| ≤
      testNorm a * testNorm (SigU (n := Fin N) Sig *ᵥ b) := cII_dot_le _ _
  have hd2 : |a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b| ≤
      testNorm (SigU (n := Fin N) Sig *ᵥ a) * testNorm b := by
    rw [cII_dot_SigU hSig]; exact cII_dot_le _ _
  have hd : ‖((a ⬝ᵥ SigU (n := Fin N) Sig *ᵥ b : ℝ) : ℂ)‖ ≤
      min (testNorm a * testNorm (SigU (n := Fin N) Sig *ᵥ b))
        (testNorm (SigU (n := Fin N) Sig *ᵥ a) * testNorm b) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_min hd1 hd2
  rw [h3]
  refine (norm_sub_le _ _).trans ?_
  exact add_le_add h1 hd

private theorem cII_SigU_vbar {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (v : Fin M ⊕ Fin N → ℝ) : SigU (n := Fin N) Sig *ᵥ vbar Sig v = v := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with i | μ
  · simp [SigU, vbar, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [SigU, vbar, fromBlocks_mulVec]

private theorem cII_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
    ∃ U : Matrix (Fin M) (Fin M) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      Sig = U * diagonal (specOf Sig) * Uᵀ ∧ ∀ i, 0 < specOf Sig i := by
  obtain ⟨U, hU, hD⟩ := exists_orth_diag hSig.1
  have h₁ : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hU
  have h₂ : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  refine ⟨U, h₂, h₁, ?_, fun i => ?_⟩
  · rw [← hD]
    simp only [← Matrix.mul_assoc]
    rw [h₂, Matrix.one_mul, Matrix.mul_assoc, h₂, Matrix.mul_one]
  · rw [specOf_eq hSig.1]
    exact hSig.eigenvalues_pos i

private theorem cII_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

private theorem cII_testNorm_SigU {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (x : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ x) =
      √(∑ i, (σ i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i) ^ 2 + ∑ μ, x (Sum.inr μ) ^ 2) := by
  have e : ∀ i, σ i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i = (Uᵀ *ᵥ (Sig *ᵥ (x ∘ Sum.inl))) i := by
    intro i
    rw [hS, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁, Matrix.one_mul,
      ← mulVec_mulVec, mulVec_diagonal]
  simp only [e, cII_sum_sq_UT h₂]
  unfold testNorm
  congr 1
  simp only [SigU, fromBlocks_mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mulVec, add_zero, zero_add, one_mulVec]
  rfl

/-- `|Σ̲ x| ≤ τ⁻¹ |x|` under (bound_Sigma) and `τ ≤ 1`. -/
private theorem cII_SigU_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ}
    (hS : SigmaAssumption τ Sig) (hτ1 : τ ≤ 1) (hτ : 0 < τ) (x : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ x) ≤ τ⁻¹ * testNorm x := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := cII_diag hS.posDef
  have hle : ∀ i, specOf Sig i ≤ τ⁻¹ := fun i => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le i
  have ht1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have ht0 : 0 ≤ τ⁻¹ := by linarith
  rw [cII_testNorm_SigU h₂ h₁ hSd]
  unfold testNorm
  rw [show τ⁻¹ * Real.sqrt (∑ s, x s ^ 2) = Real.sqrt (τ⁻¹ ^ 2 * ∑ s, x s ^ 2) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht0]]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fintype.sum_sum_type]
  have h3 : ∑ i, (specOf Sig i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i) ^ 2 ≤
      τ⁻¹ ^ 2 * ∑ i, x (Sum.inl i) ^ 2 := by
    rw [show ∑ i, x (Sum.inl i) ^ 2 = ∑ i, (Uᵀ *ᵥ (x ∘ Sum.inl)) i ^ 2 from
      (cII_sum_sq_UT h₂ (x ∘ Sum.inl)).symm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hσ i).le (hle i) 2) (sq_nonneg _)
  have h4 : ∑ μ, x (Sum.inr μ) ^ 2 ≤ τ⁻¹ ^ 2 * ∑ μ, x (Sum.inr μ) ^ 2 := by
    refine le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
    nlinarith
  linarith

end Entries

/-! ## The setting -/

section Setting

private theorem cII_N_pos {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : 1 ≤ N := by
  by_contra h
  have h0 : N = 0 := by omega
  have := hset.ratio_ge
  rw [h0] at this
  simp at this
  linarith [hset.pos]

private theorem cII_M_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : (M : ℝ) ≤ τ⁻¹ * N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast cII_N_pos hset
  have := hset.ratio_le
  rwa [div_le_iff₀ hNp] at this

private theorem cII_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption
      (cII_N_pos hset), hset.sigma⟩).densityAssumptions hset.pos

/-- `1 ≤ N η` on `𝐃(τ, N)`. -/
private theorem cII_one_le_N_im {τ : ℝ} {z : ℂ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hz : z ∈ specDomain τ N) : 1 ≤ (N : ℝ) * z.im := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
  have h2 : 1 ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1r hτ.le
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := h2
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hz.2.2.2.1 hNp.le

/-- The facts of the setting used below. -/
private structure cII_Facts (τ c : ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) : Prop where
  pos : 0 < τ
  le_one : τ ≤ 1
  N1 : 1 ≤ N
  Mle : (M : ℝ) ≤ τ⁻¹ * N
  M1 : 1 ≤ M
  sig : SigmaAssumption τ Sig
  posDef : Sig.PosDef
  im_pos : 0 < z.im
  Nim : 1 ≤ (N : ℝ) * z.im
  im_le : z.im ≤ τ⁻¹
  norm_ge : τ ≤ ‖z‖
  m_le : ‖mFun N (specOf Sig) z‖ ≤ mBoundConst τ
  Km1 : 1 ≤ mBoundConst τ
  rough1 : 1 ≤ roughConst τ c

private theorem cII_facts {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) : cII_Facts (N := N) τ c Sig z := by
  have hτ := hset.pos
  have hτ1 := hset.le_one
  have hN := cII_N_pos hset
  have hzD := hset.domain.1 hz
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hKm : 1 ≤ mBoundConst τ := by
    unfold mBoundConst genPropConst
    have h2 : (0 : ℝ) < τ / 2 := by positivity
    have h3 : τ / 2 ≤ 1 := by linarith
    rw [le_div_iff₀ (by positivity)]
    have h4 : (τ / 2) ^ 4 ≤ 1 := pow_le_one₀ h2.le h3
    nlinarith
  have hM1 : 1 ≤ M := by
    have h := hset.ratio_ge
    by_contra hM
    have : M = 0 := by omega
    rw [this] at h
    simp at h
    linarith
  refine ⟨hτ, hτ1, hN, cII_M_le hset, hM1, hset.sigma, hset.sigma.posDef, hzD.1,
    cII_one_le_N_im hN hτ hzD, hzD.2.2.2.2, hzD.2.1,
    (gen_prop_m_specDomain (cII_density hset) hzD).2.1, hKm, ?_⟩
  unfold roughConst
  have hK : 0 ≤ mBoundConst τ * max c⁻¹ 1 :=
    mul_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))
  have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
  nlinarith

/-- `‖X‖_F² = ∑_{jν} X_{jν}²`. -/
private def cII_sq (A : Matrix (Fin M) (Fin N) ℝ) : ℝ := ∑ α : Fin M × Fin N, A α.1 α.2 ^ 2

private theorem cII_sq_nonneg (A : Matrix (Fin M) (Fin N) ℝ) : 0 ≤ cII_sq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem cII_continuous_sq : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => cII_sq A := by
  unfold cII_sq
  exact continuous_finsetSum _ fun α _ => ((continuous_id.matrix_elem α.1 α.2).pow 2)

private theorem cII_opNorm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLpLin_apply, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `‖XᵀX‖ ≤ ‖X‖_F²`. -/
private theorem cII_XtX_le (A : Matrix (Fin M) (Fin N) ℝ) : ‖Aᵀ * A‖ ≤ cII_sq A := by
  have h1 : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have h2 := cII_opNorm_le A
  have h0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [h1, cII_sq, Fintype.sum_prod_type]
  calc ‖A‖ * ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, A i j ^ 2) :=
        mul_le_mul h2 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt h0

/-- `‖X^{(μ ↦ y)}‖_F² ≤ ‖X‖_F² + |y|²`. -/
private theorem cII_sq_updCol (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (y : Fin M → ℝ) :
    cII_sq (updCol A μ y) ≤ cII_sq A + ∑ j, y j ^ 2 := by
  unfold cII_sq
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have h : ∀ j, ∑ ν, updCol A μ y j ν ^ 2 ≤ ∑ ν, A j ν ^ 2 + y j ^ 2 := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ), ← Finset.add_sum_erase _ _
      (Finset.mem_univ μ)]
    have e : ∑ ν ∈ Finset.univ.erase μ, updCol A μ y j ν ^ 2 =
        ∑ ν ∈ Finset.univ.erase μ, A j ν ^ 2 := by
      refine Finset.sum_congr rfl fun ν hν => ?_
      simp [updCol, Finset.ne_of_mem_erase hν]
    rw [e]
    simp only [updCol, ite_true]
    nlinarith [sq_nonneg (A j μ)]
  calc ∑ j, ∑ ν, updCol A μ y j ν ^ 2 ≤ ∑ j, (∑ ν, A j ν ^ 2 + y j ^ 2) :=
        Finset.sum_le_sum fun j _ => h j
    _ = _ := Finset.sum_add_distrib

private theorem cII_sq_updCol_zero (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) :
    cII_sq (updCol A μ 0) ≤ cII_sq A := by
  have := cII_sq_updCol A μ 0
  simpa using this

/-- `(1 + ‖X‖_F²)/η ≥ (1 + ‖XᵀX‖)/η`, with `η ≥ N⁻¹`. -/
private theorem cII_Lam_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}
    (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ) :
    (1 + ‖Aᵀ * A‖) / z.im ≤ N * (1 + cII_sq A) := by
  rw [div_le_iff₀ hF.im_pos]
  have := cII_XtX_le A
  have h0 : 0 ≤ 1 + ‖Aᵀ * A‖ := by positivity
  have h1 : 1 + ‖Aᵀ * A‖ ≤ 1 + cII_sq A := by linarith
  have h2 := hF.Nim
  nlinarith [cII_sq_nonneg A]

end Setting

/-! ## Rough bounds on the entries -/

section Rough

/-- The admissible pairs of test vectors: not both `v̄`. -/
private def cII_Pair (Sig : Matrix (Fin M) (Fin M) ℝ) (v : Fin M ⊕ Fin N → ℝ)
    (x y : Fin M ⊕ Fin N → ℝ) : Prop :=
  (x = vbar Sig v ∧ ∃ t, y = eI t) ∨ (∃ s, x = eI s ∧ y = vbar Sig v) ∨
    (∃ s t, x = eI s ∧ y = eI t)

private theorem cII_vbar_inr_le {Sig : Matrix (Fin M) (Fin M) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    (hv : testNorm v = 1) (μ : Fin N) : |vbar Sig v (Sum.inr μ)| ≤ 1 := by
  have h : vbar Sig v (Sum.inr μ) = v (Sum.inr μ) := by simp [vbar]
  rw [h]
  have h1 : v (Sum.inr μ) ^ 2 ≤ ∑ s, v s ^ 2 :=
    Finset.single_le_sum (f := fun s => v s ^ 2) (fun s _ => sq_nonneg _) (Finset.mem_univ _)
  have h2 : ∑ s, v s ^ 2 = 1 := by
    unfold testNorm at hv
    rwa [Real.sqrt_eq_one] at hv
  rw [h2] at h1
  rw [← abs_one]
  exact sq_le_sq.1 (by simpa using h1)

private theorem cII_eI_le (s : Fin M ⊕ Fin N) (r : Fin M ⊕ Fin N) : |eI s r| ≤ 1 := by
  unfold eI
  by_cases h : r = s
  · subst h; simp
  · simp [h]

/-- `|G_{xy}| ≤ 2 τ⁻² ((1 + ‖XᵀX‖)/η + 1)` for admissible `x, y`. -/
private theorem cII_ent_G_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}
    (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) {x y : Fin M ⊕ Fin N → ℝ}
    (hxy : cII_Pair Sig v x y) :
    ‖ent (G Sig A z) x y‖ ≤ 2 * τ⁻¹ ^ 2 * ((1 + ‖Aᵀ * A‖) / z.im + 1) := by
  have hτ := hF.pos
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hF.le_one
  have hL : 0 ≤ (1 + ‖Aᵀ * A‖) / z.im + 1 := by
    have := norm_nonneg (Aᵀ * A); have := hF.im_pos; positivity
  have hSe : ∀ s : Fin M ⊕ Fin N, testNorm (SigU (n := Fin N) Sig *ᵥ eI s) ≤ τ⁻¹ := fun s => by
    have := cII_SigU_le hF.sig hF.le_one hτ (eI s)
    rwa [cII_testNorm_eI, mul_one] at this
  have hSe0 : ∀ s : Fin M ⊕ Fin N, 0 ≤ testNorm (SigU (n := Fin N) Sig *ᵥ eI s) := fun s =>
    Real.sqrt_nonneg _
  have hSv : testNorm (SigU (n := Fin N) Sig *ᵥ vbar Sig v) = 1 := by
    rw [cII_SigU_vbar hF.posDef, hv]
  have hT2 : τ⁻¹ ≤ τ⁻¹ ^ 2 := by nlinarith
  have hL1 : 1 ≤ (1 + ‖Aᵀ * A‖) / z.im + 1 := by
    have := norm_nonneg (Aᵀ * A); have := hF.im_pos
    have : 0 ≤ (1 + ‖Aᵀ * A‖) / z.im := by positivity
    linarith
  have k1 : ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ ^ 2 :=
    mul_le_mul_of_nonneg_left hT2 hL
  have k2 : (1 : ℝ) ≤ τ⁻¹ ^ 2 * ((1 + ‖Aᵀ * A‖) / z.im + 1) := by nlinarith
  have k3 : τ⁻¹ ≤ τ⁻¹ ^ 2 * ((1 + ‖Aᵀ * A‖) / z.im + 1) := by nlinarith
  rcases hxy with ⟨rfl, t, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨s, t, rfl, rfl⟩
  · refine (cII_G_bound hF.posDef A hF.im_pos _ _).trans ?_
    rw [hSv, cII_testNorm_eI]
    have h1 := min_le_right (testNorm (vbar Sig v) * testNorm (SigU (n := Fin N) Sig *ᵥ eI t))
      (1 * 1)
    have h2 : ((1 + ‖Aᵀ * A‖) / z.im + 1) * 1 * testNorm (SigU (n := Fin N) Sig *ᵥ eI t) ≤
        ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ := by
      rw [mul_one]; exact mul_le_mul_of_nonneg_left (hSe t) hL
    calc _ ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ + 1 * 1 := add_le_add h2 h1
      _ ≤ _ := by linarith
  · refine (cII_G_bound hF.posDef A hF.im_pos _ _).trans ?_
    rw [hSv, cII_testNorm_eI]
    have h1 := min_le_left (1 * 1)
      (testNorm (SigU (n := Fin N) Sig *ᵥ eI s) * testNorm (vbar Sig v))
    have h2 : ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ eI s) * 1 ≤
        ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ := by
      rw [mul_one]; exact mul_le_mul_of_nonneg_left (hSe s) hL
    calc _ ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ + 1 * 1 := add_le_add h2 h1
      _ ≤ _ := by linarith
  · refine (cII_G_bound hF.posDef A hF.im_pos _ _).trans ?_
    rw [cII_testNorm_eI, cII_testNorm_eI]
    have h1 := min_le_left (1 * testNorm (SigU (n := Fin N) Sig *ᵥ eI t))
      (testNorm (SigU (n := Fin N) Sig *ᵥ eI s) * 1)
    have h2 : ((1 + ‖Aᵀ * A‖) / z.im + 1) * testNorm (SigU (n := Fin N) Sig *ᵥ eI s) *
        testNorm (SigU (n := Fin N) Sig *ᵥ eI t) ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ ^ 2 := by
      rw [sq, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hSe s) (hSe t) (hSe0 t) (by linarith)) hL
    have h3 := hSe t
    calc _ ≤ ((1 + ‖Aᵀ * A‖) / z.im + 1) * τ⁻¹ ^ 2 + 1 * testNorm (SigU (n := Fin N) Sig *ᵥ eI t) :=
          add_le_add h2 h1
      _ ≤ _ := by linarith

/-- `|G_{xy}| ≤ 4 τ⁻² N (1 + ‖X‖_F²)` for admissible `x, y`. -/
private theorem cII_ent_G_le' {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}
    (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) {x y : Fin M ⊕ Fin N → ℝ}
    (hxy : cII_Pair Sig v x y) :
    ‖ent (G Sig A z) x y‖ ≤ 4 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
  have h := cII_ent_G_le hF A hv hxy
  have h1 := cII_Lam_le hF A
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hF.N1
  have h2 : 1 ≤ (N : ℝ) * (1 + cII_sq A) := by nlinarith [cII_sq_nonneg A]
  have h3 : 0 ≤ τ⁻¹ ^ 2 := by positivity
  nlinarith

/-- `|G^{(μ)}_{xy}| ≤ 5 τ⁻² N (1 + ‖X‖_F²)` for admissible `x, y`, through `G(X⁰)`. -/
private theorem cII_ent_Gmu_le {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}
    (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) {x y : Fin M ⊕ Fin N → ℝ}
    (hxy : cII_Pair Sig v x y) (hx : |x (Sum.inr μ)| ≤ 1) (hy : |y (Sum.inr μ)| ≤ 1) :
    ‖ent (Gmu Sig A z μ) x y‖ ≤ 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
  rw [cII_ent_Gmu hF.posDef A hF.im_pos μ]
  have h1 := cII_ent_G_le' hF (updCol A μ 0) hv hxy
  have h2 := cII_sq_updCol_zero A μ
  have hτ := hF.pos
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hF.le_one
  have hz : ‖z⁻¹‖ ≤ τ⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ hτ hF.norm_ge
  have h3 : ‖((x (Sum.inr μ) : ℂ) * (y (Sum.inr μ) : ℂ)) * z⁻¹‖ ≤ τ⁻¹ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have : |x (Sum.inr μ)| * |y (Sum.inr μ)| ≤ 1 := by
      nlinarith [abs_nonneg (x (Sum.inr μ)), abs_nonneg (y (Sum.inr μ))]
    nlinarith [norm_nonneg z⁻¹, abs_nonneg (x (Sum.inr μ)), abs_nonneg (y (Sum.inr μ))]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hF.N1
  have h4 : 1 ≤ (N : ℝ) * (1 + cII_sq A) := by nlinarith [cII_sq_nonneg A]
  have h5 : 4 * τ⁻¹ ^ 2 * (N * (1 + cII_sq (updCol A μ 0))) ≤
      4 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
    gcongr
  have h6 : τ⁻¹ ≤ τ⁻¹ ^ 2 := by nlinarith
  refine (norm_add_le _ _).trans ?_
  nlinarith

end Rough

/-! ## The rough level `U = c_U N² (1 + ‖X‖_F²)²` -/

section Level

/-- The constant `c_U` of the rough level. -/
private def cII_cU (τ c : ℝ) : ℝ := 20 * τ⁻¹ ^ 3 * (roughConst τ c + mBoundConst τ + 2)

/-- The rough level `U(X) = c_U N² (1 + ‖X‖_F²)²` bounding every factor deterministically. -/
private def cII_U (τ c : ℝ) (A : Matrix (Fin M) (Fin N) ℝ) : ℝ :=
  cII_cU τ c * (N : ℝ) ^ 2 * (1 + cII_sq A) ^ 2

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_U_ge (A : Matrix (Fin M) (Fin N) ℝ) :
    20 * τ⁻¹ ^ 3 * (roughConst τ c + mBoundConst τ + 2) * ((N : ℝ) * (1 + cII_sq A)) ^ 2 ≤
      cII_U τ c A := by
  unfold cII_U cII_cU; rw [mul_pow]; ring_nf; exact le_rfl

private theorem cII_base_ge (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ) :
    1 ≤ (N : ℝ) * (1 + cII_sq A) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hF.N1
  nlinarith [cII_sq_nonneg A]

private theorem cII_U_ge_mul (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {a : ℝ} (ha : a ≤ 20 * τ⁻¹ ^ 3 * (roughConst τ c + mBoundConst τ + 2)) :
    a * ((N : ℝ) * (1 + cII_sq A)) ≤ cII_U τ c A := by
  have h1 := cII_base_ge hF A
  have hc : 0 ≤ 20 * τ⁻¹ ^ 3 * (roughConst τ c + mBoundConst τ + 2) := by
    have := hF.rough1; have := hF.Km1; have := hF.pos; positivity
  refine le_trans ?_ (cII_U_ge A)
  rcases le_or_gt a 0 with h | h
  · nlinarith
  · rw [sq]
    calc a * ((N : ℝ) * (1 + cII_sq A))
        ≤ (20 * τ⁻¹ ^ 3 * (roughConst τ c + mBoundConst τ + 2)) * ((N : ℝ) * (1 + cII_sq A)) :=
          mul_le_mul_of_nonneg_right ha (by linarith)
      _ ≤ _ := by
          have hx : (N : ℝ) * (1 + cII_sq A) ≤ (N * (1 + cII_sq A)) * (N * (1 + cII_sq A)) :=
            le_mul_of_one_le_left (by linarith) h1
          exact mul_le_mul_of_nonneg_left hx hc

private theorem cII_U_one (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ) :
    1 ≤ cII_U τ c A := by
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
  have h := cII_U_ge_mul hF A (a := 1) (by nlinarith [hF.rough1, hF.Km1])
  have := cII_base_ge hF A
  linarith

private theorem cII_U_nonneg (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ) :
    0 ≤ cII_U τ c A := zero_le_one.trans (cII_U_one hF A)

private theorem cII_ofT_ne (b : Bool) : Letter.ofT b ≠ .V := by
  cases b <;> simp [Letter.ofT]

private theorem cII_ofS_ne (b : Bool) : Letter.ofS b ≠ .V := by
  cases b <;> simp [Letter.ofS]

/-- No factor of a nonempty word is `G_{v̄v̄}`. -/
private theorem cII_not_VV {k : ℕ} (w : Word (k + 1)) (l : Fin (k + 2)) :
    ¬(factorX w l = .V ∧ factorY w l = .V) := by
  rintro ⟨hx, hy⟩
  unfold factorX at hx
  unfold factorY at hy
  split_ifs at hx hy with h1 h2
  · exact cII_ofT_ne _ hy
  · omega
  · exact cII_ofS_ne _ hx
  · exact cII_ofS_ne _ hx

private theorem cII_letVec_pair (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) (x y : Letter)
    (hxy : ¬(x = .V ∧ y = .V)) : cII_Pair Sig v (letVec Sig v i μ x) (letVec Sig v i μ y) := by
  cases x <;> cases y
  · exact absurd ⟨rfl, rfl⟩ hxy
  all_goals first
    | exact Or.inl ⟨rfl, _, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, _, rfl, rfl⟩)

private theorem cII_letVec_inr {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M)
    (μ : Fin N) (x : Letter) : |letVec Sig v i μ x (Sum.inr μ)| ≤ 1 := by
  cases x
  · exact cII_vbar_inr_le hv μ
  · exact cII_eI_le _ _
  · exact cII_eI_le _ _

private theorem cII_Gmu_letter (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (x y : Letter)
    (hxy : ¬(x = .V ∧ y = .V)) :
    ‖ent (Gmu Sig A z μ) (letVec Sig v i μ x) (letVec Sig v i μ y)‖ ≤
      5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) :=
  cII_ent_Gmu_le hF A μ hv (cII_letVec_pair v i μ x y hxy) (cII_letVec_inr hv i μ x)
    (cII_letVec_inr hv i μ y)

private theorem cII_colC_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (x : Letter) (j : Fin M) :
    ‖colC Sig A z (letVec Sig v i μ x) μ j‖ ≤ 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
  unfold colC
  refine cII_ent_Gmu_le hF A μ hv ?_ (cII_letVec_inr hv i μ x) (cII_eI_le _ _)
  cases x
  · exact Or.inl ⟨rfl, _, rfl⟩
  all_goals exact Or.inr (Or.inr ⟨_, _, rfl, rfl⟩)

private theorem cII_rowC_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (x : Letter) (j : Fin M) :
    ‖rowC Sig A z (letVec Sig v i μ x) μ j‖ ≤ 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
  unfold rowC
  refine cII_ent_Gmu_le hF A μ hv ?_ (cII_eI_le _ _) (cII_letVec_inr hv i μ x)
  cases x
  · exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  all_goals exact Or.inr (Or.inr ⟨_, _, rfl, rfl⟩)

/-- `∑_j |X_{jμ}| ≤ τ⁻¹ N (1 + ‖X‖_F²)`. -/
private theorem cII_col_sum_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) : ∑ j, |A j μ| ≤ τ⁻¹ * N * (1 + cII_sq A) := by
  have h1 : ∀ j, |A j μ| ≤ 1 + A j μ ^ 2 := fun j => by
    nlinarith [abs_nonneg (A j μ), sq_abs (A j μ)]
  have h2 : ∑ j, A j μ ^ 2 ≤ cII_sq A := by
    unfold cII_sq
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun j _ =>
      Finset.single_le_sum (f := fun ν => A j ν ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hF.M1
  calc ∑ j, |A j μ| ≤ ∑ j, (1 + A j μ ^ 2) := Finset.sum_le_sum fun j _ => h1 j
    _ = M + ∑ j, A j μ ^ 2 := by simp [Finset.sum_add_distrib]
    _ ≤ M * (1 + cII_sq A) := by nlinarith [cII_sq_nonneg A]
    _ ≤ τ⁻¹ * N * (1 + cII_sq A) := by
        have := cII_sq_nonneg A
        exact mul_le_mul_of_nonneg_right hF.Mle (by linarith)

/-- A linear form of the column `μ` with coefficients at most `10 τ⁻² N (1 + ‖X‖_F²)` is at most
`U(X)`. -/
private theorem cII_form_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) (cv : Fin M → ℂ) (hcv : ∀ j, ‖cv j‖ ≤ 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A))) :
    ‖linForm cv fun j => A j μ‖ ≤ cII_U τ c A := by
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  have hb := cII_base_ge hF A
  have hs := cII_col_sum_le hF A μ
  have h1 : ‖linForm cv fun j => A j μ‖ ≤ 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) * ∑ j, |A j μ| := by
    unfold linForm
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcv j) (abs_nonneg _)
  refine h1.trans ?_
  have h2 : 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) * ∑ j, |A j μ| ≤
      10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) * (τ⁻¹ * N * (1 + cII_sq A)) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  refine h2.trans ?_
  have h3 : 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) * (τ⁻¹ * N * (1 + cII_sq A)) =
      10 * τ⁻¹ ^ 3 * ((N : ℝ) * (1 + cII_sq A)) ^ 2 := by ring
  rw [h3]
  refine le_trans ?_ (cII_U_ge A)
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have := hF.rough1; have := hF.Km1
  have h4 : 0 ≤ τ⁻¹ ^ 3 := by positivity
  nlinarith

private theorem cII_list_prod_le {α : Type*} (l : List α) (f : α → ℂ) {U : ℝ} (hU : 1 ≤ U)
    (h : ∀ c ∈ l, ‖f c‖ ≤ U) : ‖(l.map f).prod‖ ≤ U ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul]
    have ha := h a (List.mem_cons_self ..)
    have hl := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [pow_succ']
    exact mul_le_mul ha hl (norm_nonneg _) (by linarith)

private theorem cII_brackScal_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (x y : Letter)
    (hxy : ¬(x = .V ∧ y = .V)) (s : Fin 3) :
    ‖brackScal Sig A z v i μ x y s‖ ≤ cII_U τ c A := by
  have hU := cII_U_one hF A
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  unfold brackScal
  split_ifs
  · refine (cII_Gmu_letter hF A hv i μ x y hxy).trans ?_
    refine cII_U_ge_mul hF A ?_
    have := hF.rough1; have := hF.Km1
    have h3 : τ⁻¹ ^ 2 ≤ τ⁻¹ ^ 3 := pow_le_pow_right₀ hT (by norm_num)
    nlinarith
  all_goals simp; linarith

private theorem cII_mem_brackForms {A : Matrix (Fin M) (Fin N) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    {i : Fin M} {μ : Fin N} {x y : Letter} {s : Fin 3} {cv : Fin M → ℂ}
    (h : cv ∈ brackForms Sig A z v i μ x y s) :
    cv = colC Sig A z (letVec Sig v i μ x) μ ∨ cv = rowC Sig A z (letVec Sig v i μ y) μ := by
  unfold brackForms at h
  split_ifs at h <;>
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.nil_append,
      List.append_nil] at h <;> tauto

private theorem cII_brack_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) (x y : Letter)
    (hxy : ¬(x = .V ∧ y = .V)) (s : Fin 3) :
    ‖brack Sig A z v i μ x y s‖ ≤ cII_U τ c A ^ 3 := by
  have hU := cII_U_one hF A
  unfold brack
  rw [norm_mul]
  have h1 := cII_brackScal_le hF A hv i μ x y hxy s
  have hc : ∀ cv ∈ brackForms Sig A z v i μ x y s, ‖linForm cv fun j => A j μ‖ ≤ cII_U τ c A := by
    intro cv hcv
    refine cII_form_le hF A μ cv fun j => ?_
    have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
    have hb := cII_base_ge hF A
    have k : 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) ≤ 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
      have : 0 ≤ τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by positivity
      linarith
    rcases cII_mem_brackForms hcv with rfl | rfl
    · exact (cII_colC_le hF A hv i μ _ j).trans k
    · exact (cII_rowC_le hF A hv i μ _ j).trans k
  have h2 := cII_list_prod_le _ _ hU hc
  have hlen : (brackForms Sig A z v i μ x y s).length ≤ 2 := by
    rw [brackForms_length]
    unfold degTab
    split_ifs <;> omega
  have h3 : cII_U τ c A ^ (brackForms Sig A z v i μ x y s).length ≤ cII_U τ c A ^ 2 :=
    pow_le_pow_right₀ hU hlen
  calc ‖brackScal Sig A z v i μ x y s‖ * ‖((brackForms Sig A z v i μ x y s).map
        fun c => linForm c fun j => A j μ).prod‖ ≤ cII_U τ c A * cII_U τ c A ^ 2 :=
        mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by linarith)
    _ = cII_U τ c A ^ 3 := by ring

end Level

section Level2

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_PiZ_mu (Sig : Matrix (Fin M) (Fin M) ℝ) (z : ℂ) (μ : Fin N) :
    PiZ N Sig z (Sum.inr μ) (Sum.inr μ) = mFun N (specOf Sig) z := by
  simp [PiZ, piMat]

/-- `A(w₀, 0) = (G(X⁰) − Π)_{v̄v̄} + v̄(μ)² (z⁻¹ + Π_μμ)`. -/
private theorem cII_emptyScal_zero {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) :
    emptyScal Sig A z v μ 0 = ent (G Sig (updCol A μ 0) z - PiZ N Sig z) (vbar Sig v) (vbar Sig v) +
      ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ 2 * (z⁻¹ + PiZ N Sig z (Sum.inr μ) (Sum.inr μ)) := by
  simp only [emptyScal, ↓reduceIte, cII_ent_Gmu hSig A hz μ, cII_ent_sub]
  ring

private theorem cII_emptyScal_le {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M)
    (μ : Fin N) (s : Fin 3) : ‖emptyScal Sig A z v μ s‖ ≤ cII_U τ c A := by
  have hF := cII_facts hset hz
  have hU := cII_U_one hF A
  fin_cases s
  · simp only [Fin.zero_eta]
    rw [cII_emptyScal_zero hF.posDef A hF.im_pos v μ]
    have h1 : ‖ent (G Sig (updCol A μ 0) z - PiZ N Sig z) (vbar Sig v) (vbar Sig v)‖ ≤
        roughConst τ c * (N * (1 + cII_sq A)) := by
      have h := norm_wordA_rough hset hz (updCol A μ 0) v hv i μ 0 (fun x => Fin.elim0 x)
      simp only [wordA, zero_add, pow_one] at h
      refine h.trans ?_
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hF.rough1)
      refine (cII_Lam_le hF _).trans ?_
      have := cII_sq_updCol_zero A μ
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith
    have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
    have hvμ := cII_vbar_inr_le (Sig := Sig) hv μ
    have h2 : ‖((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ 2 * (z⁻¹ + PiZ N Sig z (Sum.inr μ) (Sum.inr μ))‖
        ≤ τ⁻¹ + mBoundConst τ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, cII_PiZ_mu]
      have hz' : ‖z⁻¹‖ ≤ τ⁻¹ := by rw [norm_inv]; exact inv_anti₀ hF.pos hF.norm_ge
      have h3 : ‖z⁻¹ + mFun N (specOf Sig) z‖ ≤ τ⁻¹ + mBoundConst τ :=
        (norm_add_le _ _).trans (add_le_add hz' hF.m_le)
      have h4 : |vbar Sig v (Sum.inr μ)| ^ 2 ≤ 1 := by
        have := abs_nonneg (vbar Sig v (Sum.inr μ)); nlinarith
      calc |vbar Sig v (Sum.inr μ)| ^ 2 * ‖z⁻¹ + mFun N (specOf Sig) z‖ ≤
            1 * (τ⁻¹ + mBoundConst τ) :=
            mul_le_mul h4 h3 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    refine (norm_add_le _ _).trans ?_
    have hb := cII_base_ge hF A
    have hK := hF.Km1
    have hR := hF.rough1
    have h5 : roughConst τ c * (N * (1 + cII_sq A)) + (τ⁻¹ + mBoundConst τ) ≤
        (roughConst τ c + τ⁻¹ + mBoundConst τ) * (N * (1 + cII_sq A)) := by nlinarith
    refine (add_le_add h1 h2).trans (h5.trans (cII_U_ge_mul hF A ?_))
    have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
    have h6 : τ⁻¹ ≤ τ⁻¹ ^ 3 := by
      calc τ⁻¹ = τ⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ τ⁻¹ ^ 3 := pow_le_pow_right₀ hT (by norm_num)
    nlinarith
  · simpa [emptyScal] using hU
  · simpa [emptyScal] using hU

private theorem cII_tagA_le {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M)
    (μ : Fin N) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    ‖tagA Sig A z v i μ n w σ‖ ≤ cII_U τ c A ^ (3 * (n + 1)) := by
  have hF := cII_facts hset hz
  have hU := cII_U_one hF A
  cases n with
  | zero =>
    simp only [tagA, norm_mul, zero_add, mul_one]
    have h1 := cII_emptyScal_le hset hz A hv i μ (σ 0)
    have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
    have hb := cII_base_ge hF A
    have k : 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) ≤ 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
      have : 0 ≤ τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by positivity
      linarith
    have hc : ∀ cv ∈ emptyForms Sig A z v μ (σ 0), ‖linForm cv fun j => A j μ‖ ≤ cII_U τ c A := by
      intro cv hcv
      refine cII_form_le hF A μ cv fun j => ?_
      have h1 := cII_colC_le hF A hv i μ .V j
      have h2 := cII_rowC_le hF A hv i μ .V j
      simp only [letVec] at h1 h2
      unfold emptyForms at hcv
      split_ifs at hcv
      · simp at hcv
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcv
        rcases hcv with rfl | rfl
        · exact h1.trans k
        · exact h2.trans k
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcv
        subst hcv
        refine (norm_add_le _ _).trans ?_
        have : 10 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) =
            5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) + 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by ring
        rw [this]
        exact add_le_add h1 h2
    have h2 := cII_list_prod_le _ _ hU hc
    have hlen : (emptyForms Sig A z v μ (σ 0)).length ≤ 2 := by
      unfold emptyForms; split_ifs <;> simp
    have h3 : cII_U τ c A ^ (emptyForms Sig A z v μ (σ 0)).length ≤ cII_U τ c A ^ 2 :=
      pow_le_pow_right₀ hU hlen
    calc _ ≤ cII_U τ c A * cII_U τ c A ^ 2 :=
          mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by linarith)
      _ = cII_U τ c A ^ 3 := by ring
  | succ k =>
    simp only [tagA]
    rw [norm_prod]
    calc ∏ l : Fin (k + 2), ‖brack Sig A z v i μ (factorX w l) (factorY w l) (σ l)‖
        ≤ ∏ _l : Fin (k + 2), cII_U τ c A ^ 3 :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ =>
            cII_brack_le hF A hv i μ _ _ (cII_not_VV w l) _
      _ = cII_U τ c A ^ (3 * (k + 1 + 1)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

private theorem cII_tagMu_le {n : ℕ} (σ : Fin (n + 1) → Fin 3) : tagMu σ ≤ n + 1 := by
  unfold tagMu
  calc ∑ l, (if σ l = 0 then 0 else 1) ≤ ∑ _l : Fin (n + 1), 1 :=
        Finset.sum_le_sum fun l _ => by split_ifs <;> omega
    _ = n + 1 := by simp

private theorem cII_Gmumu_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ cII_U τ c A := by
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  have h := cII_ent_G_le' hF A (v := eI (Sum.inr μ)) (cII_testNorm_eI _)
    (x := eI (Sum.inr μ)) (y := eI (Sum.inr μ)) (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))
  rw [ent_eI_eI] at h
  refine h.trans (cII_U_ge_mul hF A ?_)
  have := hF.rough1; have := hF.Km1
  have h3 : τ⁻¹ ^ 2 ≤ τ⁻¹ ^ 3 := pow_le_pow_right₀ hT (by norm_num)
  nlinarith

private theorem cII_Qmu_eq (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) : Qmu Sig A z μ =
      ∑ j, ∑ j', (A j μ : ℂ) * Gmu Sig A z μ (Sum.inl j) (Sum.inl j') * (A j' μ : ℂ) := by
  have h : updCol A μ (fun j => A j μ) = A := by
    funext j ν; by_cases h : ν = μ <;> simp [updCol, h]
  conv_lhs => rw [← h]
  rw [Qmu_updCol]

private theorem cII_Gmu_jk (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) (j k : Fin M) :
    ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl k)‖ ≤ 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) := by
  have h := cII_ent_Gmu_le hF A μ (v := eI (Sum.inl j)) (cII_testNorm_eI _)
    (x := eI (Sum.inl j)) (y := eI (Sum.inl k)) (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))
    (cII_eI_le _ _) (cII_eI_le _ _)
  rwa [ent_eI_eI] at h

private theorem cII_Qmu_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) : ‖Qmu Sig A z μ‖ ≤ cII_U τ c A := by
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  have hb := cII_base_ge hF A
  set g := 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) with hg
  have hg0 : 0 ≤ g := by positivity
  rw [cII_Qmu_eq]
  have h1 : ‖∑ j, ∑ j', (A j μ : ℂ) * Gmu Sig A z μ (Sum.inl j) (Sum.inl j') * (A j' μ : ℂ)‖ ≤
      g * (∑ j, |A j μ|) ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j' _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have := cII_Gmu_jk hF A μ j j'
    have h0 := abs_nonneg (A j μ)
    have h0' := abs_nonneg (A j' μ)
    calc |A j μ| * ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j')‖ * |A j' μ| ≤
          |A j μ| * g * |A j' μ| := by
          gcongr
      _ = g * (|A j μ| * |A j' μ|) := by ring
  have h2 : (∑ j, |A j μ|) ^ 2 ≤ M * ∑ j, |A j μ| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M))) (f := fun j => |A j μ|)
    simpa using this
  have h3 : ∑ j, |A j μ| ^ 2 ≤ cII_sq A := by
    unfold cII_sq
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [sq_abs]
    exact Finset.single_le_sum (f := fun ν => A j ν ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ)
  have hS := cII_sq_nonneg A
  have h4 : (∑ j, |A j μ|) ^ 2 ≤ τ⁻¹ * N * (1 + cII_sq A) := by
    have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    calc (∑ j, |A j μ|) ^ 2 ≤ M * ∑ j, |A j μ| ^ 2 := h2
      _ ≤ (τ⁻¹ * N) * (1 + cII_sq A) := mul_le_mul hF.Mle (by linarith) (by positivity)
          (by positivity)
      _ = _ := by ring
  refine h1.trans ?_
  calc g * (∑ j, |A j μ|) ^ 2 ≤ g * (τ⁻¹ * N * (1 + cII_sq A)) := mul_le_mul_of_nonneg_left h4 hg0
    _ = (5 * τ⁻¹ ^ 3) * (N * (1 + cII_sq A)) ^ 2 := by rw [hg]; ring
    _ ≤ _ := by
        refine le_trans ?_ (cII_U_ge A)
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have := hF.rough1; have := hF.Km1
        have h5 : 0 ≤ τ⁻¹ ^ 3 := by positivity
        nlinarith

private theorem cII_Ymu_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) : ‖Ymu Sig A z μ‖ ≤ cII_U τ c A := by
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  have hb := cII_base_ge hF A
  have hN : (0 : ℝ) < N := by have := hF.N1; exact_mod_cast this
  unfold Ymu
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ j, Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖ ≤
      M * (5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖Gmu Sig A z μ (Sum.inl j) (Sum.inl j)‖ ≤
          ∑ _j : Fin M, 5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)) :=
          Finset.sum_le_sum fun j _ => cII_Gmu_jk hF A μ j j
      _ = _ := by simp
  have h2 : (N : ℝ)⁻¹ * (M * (5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)))) ≤
      5 * τ⁻¹ ^ 3 * (N * (1 + cII_sq A)) := by
    have hM := hF.Mle
    have e : (N : ℝ)⁻¹ * (M * (5 * τ⁻¹ ^ 2 * (N * (1 + cII_sq A)))) =
        (M : ℝ) * (5 * τ⁻¹ ^ 2 * (1 + cII_sq A)) := by field_simp
    rw [e]
    have : (M : ℝ) * (5 * τ⁻¹ ^ 2 * (1 + cII_sq A)) ≤ (τ⁻¹ * N) * (5 * τ⁻¹ ^ 2 * (1 + cII_sq A)) :=
      mul_le_mul_of_nonneg_right hM (by have := cII_sq_nonneg A; positivity)
    nlinarith
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (h2.trans (cII_U_ge_mul hF A ?_))
  have := hF.rough1; have := hF.Km1
  have h5 : 0 ≤ τ⁻¹ ^ 3 := by positivity
  nlinarith

/-- `|(−z − Y_μ)⁻¹| ≤ η⁻¹ ≤ N ≤ U(X)`. -/
private theorem cII_zY_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) : ‖(-z - Ymu Sig A z μ)⁻¹‖ ≤ cII_U τ c A ∧ -z - Ymu Sig A z μ ≠ 0 := by
  have h := (calY_rough hF.posDef A hF.im_pos μ).1
  have hη := hF.im_pos
  have h1 : z.im ≤ ‖-z - Ymu Sig A z μ‖ := by
    have := Complex.abs_im_le_norm (-z - Ymu Sig A z μ)
    have h2 : z.im ≤ |(-z - Ymu Sig A z μ).im| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hne : -z - Ymu Sig A z μ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; linarith
  refine ⟨?_, hne⟩
  rw [norm_inv]
  have h3 : ‖-z - Ymu Sig A z μ‖⁻¹ ≤ z.im⁻¹ := inv_anti₀ hη h1
  have h4 : z.im⁻¹ ≤ N := by
    rw [inv_le_iff_one_le_mul₀ hη]; linarith [hF.Nim]
  have hb := cII_base_ge hF A
  refine h3.trans (h4.trans ?_)
  have h5 : (N : ℝ) ≤ N * (1 + cII_sq A) := by
    have := cII_sq_nonneg A; have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; nlinarith
  refine h5.trans ?_
  have := cII_U_ge_mul hF A (a := 1) (by
    have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
    have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
    nlinarith [hF.rough1, hF.Km1])
  linarith

/-- `|𝒴_{μ,k}| ≤ (K+1) 2^K u^{2K+1}` when `|Y_μ|, |(−z−Y_μ)⁻¹| ≤ u`, `u ≥ 1`. -/
private theorem cII_calY_le {Y : ℂ} {u : ℝ} (hu : 1 ≤ u) (hY : ‖Y‖ ≤ u) (hw : ‖(-z - Y)⁻¹‖ ≤ u)
    (K k : ℕ) : ‖calY z Y K k‖ ≤ (K + 1) * 2 ^ K * u ^ (2 * K + 1) := by
  unfold calY
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ t ∈ Finset.Icc k K, ‖(-z - Y)⁻¹ ^ (t + 1) * (t.choose k : ℂ) * (-Y) ^ (t - k)‖ ≤
      2 ^ K * u ^ (2 * K + 1) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_natCast]
    have h1 : ‖(-z - Y)⁻¹‖ ^ (t + 1) ≤ u ^ (K + 1) :=
      (pow_le_pow_left₀ (norm_nonneg _) hw _).trans (pow_le_pow_right₀ hu (by omega))
    have h2 : ((t.choose k : ℕ) : ℝ) ≤ 2 ^ K := by
      have := Nat.choose_le_two_pow t k
      have h' : (2 : ℕ) ^ t ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) ht.2
      exact_mod_cast this.trans h'
    have h3 : ‖Y‖ ^ (t - k) ≤ u ^ K :=
      (pow_le_pow_left₀ (norm_nonneg _) hY _).trans (pow_le_pow_right₀ hu (by omega))
    calc ‖(-z - Y)⁻¹‖ ^ (t + 1) * ((t.choose k : ℕ) : ℝ) * ‖Y‖ ^ (t - k)
        ≤ u ^ (K + 1) * 2 ^ K * u ^ K := by
          gcongr
      _ = 2 ^ K * u ^ (2 * K + 1) := by ring
  calc ∑ t ∈ Finset.Icc k K, ‖(-z - Y)⁻¹ ^ (t + 1) * (t.choose k : ℂ) * (-Y) ^ (t - k)‖
      ≤ ∑ _t ∈ Finset.Icc k K, 2 ^ K * u ^ (2 * K + 1) := Finset.sum_le_sum hterm
    _ = (Finset.Icc k K).card * (2 ^ K * u ^ (2 * K + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K + 1) * (2 ^ K * u ^ (2 * K + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (Finset.Icc k K).card ≤ K + 1 := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast this
    _ = _ := by ring

end Level2

/-! ## The integrand and its truncation -/

section Integrand

/-- `P_μ = ∑_{k ≤ K} 𝒴_{μ,k} Q_μ^k`, the truncation of (Gmumu_exp2). -/
private def cII_P (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (μ : Fin N) (K : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (K + 1), calY z (Ymu Sig A z μ) K k * Qmu Sig A z μ ^ k

/-- `∏_r c_r(A(w_r, σ_r) g^{|σ_r|_μ})`, at `g = G_μμ` the integrand of (sec8 2) without
`v̄(μ)^{d_v}`. -/
private def cII_T (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (g : ℂ) : ℂ :=
  ∏ r, conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) (σs r) * g ^ tagMu (σs r))

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_P_le (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) (K : ℕ) :
    ‖cII_P Sig A z μ K‖ ≤ ((K + 1) ^ 2 * 2 ^ K) * cII_U τ c A ^ (3 * K + 1) := by
  have hU := cII_U_one hF A
  have hY := cII_Ymu_le hF A μ
  have hw := (cII_zY_le hF A μ).1
  have hQ := cII_Qmu_le hF A μ
  unfold cII_P
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.range (K + 1), ‖calY z (Ymu Sig A z μ) K k * Qmu Sig A z μ ^ k‖
      ≤ ∑ _k ∈ Finset.range (K + 1), (K + 1) * 2 ^ K * cII_U τ c A ^ (2 * K + 1) *
          cII_U τ c A ^ K := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [norm_mul, norm_pow]
        have h1 := cII_calY_le hU hY hw K k
        have h2 : ‖Qmu Sig A z μ‖ ^ k ≤ cII_U τ c A ^ K :=
          (pow_le_pow_left₀ (norm_nonneg _) hQ _).trans
            (pow_le_pow_right₀ hU (by rw [Finset.mem_range] at hk; omega))
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

private theorem cII_T_le {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M)
    (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) {g : ℂ}
    {cg : ℝ} {a : ℕ} (hcg : 1 ≤ cg) (hg : ‖g‖ ≤ cg * cII_U τ c A ^ a) :
    ‖cII_T Sig A z v i μ ns ws σs cs g‖ ≤ (cg * cII_U τ c A ^ (a + 3)) ^ (p + 3) := by
  have hF := cII_facts hset hz
  have hU := cII_U_one hF A
  have hgU : 1 ≤ cg * cII_U τ c A ^ a := one_le_mul_of_one_le_of_one_le hcg (one_le_pow₀ hU)
  unfold cII_T
  rw [norm_prod]
  calc ∏ r, ‖conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) (σs r) * g ^ tagMu (σs r))‖
      ≤ ∏ r, (cg * cII_U τ c A ^ (a + 3)) ^ (ns r + 1) := by
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => ?_
        rw [cII_norm_conjIf, norm_mul, norm_pow]
        have h1 := cII_tagA_le hset hz A hv i μ (ns r) (ws r) (σs r)
        have h2 : ‖g‖ ^ tagMu (σs r) ≤ (cg * cII_U τ c A ^ a) ^ (ns r + 1) :=
          (pow_le_pow_left₀ (norm_nonneg _) hg _).trans
            (pow_le_pow_right₀ hgU (cII_tagMu_le _))
        calc ‖tagA Sig A z v i μ (ns r) (ws r) (σs r)‖ * ‖g‖ ^ tagMu (σs r)
            ≤ cII_U τ c A ^ (3 * (ns r + 1)) * (cg * cII_U τ c A ^ a) ^ (ns r + 1) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (cg * cII_U τ c A ^ (a + 3)) ^ (ns r + 1) := by
              rw [mul_pow cg, mul_pow cg, ← pow_mul, ← pow_mul, mul_left_comm, ← pow_add]
              congr 2; ring
    _ = (cg * cII_U τ c A ^ (a + 3)) ^ (∑ r, (ns r + 1)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = (cg * cII_U τ c A ^ (a + 3)) ^ (p + 3) := by
        rw [Finset.sum_add_distrib, hns]; simp [add_comm]

end Integrand

/-! ## Moments -/

section Moments

private theorem cII_measurable_X {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) : Measurable X :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => hX.measurable i μ

/-- The moment constant `2^q (1 + L^q C'_{2q})`. -/
private def cII_KW (L : ℝ) (C : ℕ → ℝ) (q : ℕ) : ℝ := 2 ^ q * (1 + L ^ q * max (C (2 * q)) 0)

private theorem cII_KW_nonneg {L : ℝ} (hL : 0 ≤ L) (C : ℕ → ℝ) (q : ℕ) : 0 ≤ cII_KW L C q := by
  unfold cII_KW
  have : 0 ≤ max (C (2 * q)) 0 := le_max_right _ _
  positivity

/-- Moments of `1 + ∑_{α ∈ ι} Y_α²` for a finite family with `E|√N Y_α|^{2q} ≤ C_{2q}`:
`E(1 + ∑ Y_α²)^q ≤ 2^q (1 + (|ι|/N)^q C'_{2q})`. -/
private theorem cII_moment_family {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {ι : Type*} [Fintype ι] {C : ℕ → ℝ}
    (Y : ι → Ω → ℝ) (hYm : ∀ a, Measurable (Y a))
    (hYi : ∀ (q : ℕ) a, Integrable fun ω => |Real.sqrt N * Y a ω| ^ q)
    (hYle : ∀ (q : ℕ) a, ∫ ω, |Real.sqrt N * Y a ω| ^ q ≤ C q) (hN : 1 ≤ N) {L : ℝ}
    (hL : 0 ≤ L) (hcard : (Fintype.card ι : ℝ) ≤ L * N) (q : ℕ) :
    Integrable (fun ω => (1 + ∑ a, Y a ω ^ 2) ^ q) ∧
      ∫ ω, (1 + ∑ a, Y a ω ^ 2) ^ q ≤ cII_KW L C q := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hS0 : ∀ ω, 0 ≤ ∑ a, Y a ω ^ 2 := fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨by simp, ?_⟩
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    unfold cII_KW
    have : 0 ≤ max (C (2 * 0)) 0 := le_max_right _ _
    simp only [pow_zero, one_mul]
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  set C' := max (C (2 * (n + 1))) 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpow : ∀ t : ℝ, (t ^ 2) ^ (n + 1) =
      ((N : ℝ) ^ (n + 1))⁻¹ * |Real.sqrt N * t| ^ (2 * (n + 1)) := by
    intro t
    rw [pow_mul, sq_abs, mul_pow, Real.sq_sqrt hNp.le, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos hNp _).ne', one_mul]
  have hXi : ∀ a, Integrable fun ω => (Y a ω ^ 2) ^ (n + 1) := by
    intro a
    simp_rw [hpow]
    exact (hYi (2 * (n + 1)) a).const_mul _
  have hXle : ∀ a, ∫ ω, (Y a ω ^ 2) ^ (n + 1) ≤ ((N : ℝ) ^ (n + 1))⁻¹ * C' := by
    intro a
    simp_rw [hpow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((hYle (2 * (n + 1)) a).trans (le_max_left _ _))
      (by positivity)
  set cd : ℝ := ((Finset.univ : Finset ι).card : ℝ) with hcd
  have hcd' : cd = Fintype.card ι := by rw [hcd, Finset.card_univ]
  have hcd0 : 0 ≤ cd := by rw [hcd]; positivity
  have hSi : Integrable fun ω => ∑ a, (Y a ω ^ 2) ^ (n + 1) :=
    integrable_finsetSum _ fun a _ => hXi a
  set g : Ω → ℝ := fun ω => 2 ^ n * (1 + cd ^ n * ∑ a, (Y a ω ^ 2) ^ (n + 1)) with hg
  have hgi : Integrable g := ((integrable_const _).add (hSi.const_mul _)).const_mul _
  have hle : ∀ ω, (1 + ∑ a, Y a ω ^ 2) ^ (n + 1) ≤ g ω := by
    intro ω
    have h1 := add_pow_le zero_le_one (hS0 ω) (n + 1)
    have h2 : (∑ a, Y a ω ^ 2) ^ (n + 1) ≤ cd ^ n * ∑ a, (Y a ω ^ 2) ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => sq_nonneg _) n
    simp only [Nat.add_sub_cancel, one_pow] at h1
    calc _ ≤ _ := h1
      _ ≤ g ω := by
          simp only [hg]
          gcongr
  have hmeas : Measurable fun ω => (1 + ∑ a, Y a ω ^ 2) ^ (n + 1) :=
    (measurable_const.add (Finset.measurable_sum _ fun a _ => (hYm a).pow_const 2)).pow_const _
  have hWi : Integrable fun ω => (1 + ∑ a, Y a ω ^ 2) ^ (n + 1) :=
    hgi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by have := hS0 ω; positivity)]; exact hle ω)
  refine ⟨hWi, ?_⟩
  have hgval : ∫ ω, g ω = 2 ^ n * (1 + cd ^ n * ∑ a, ∫ ω, (Y a ω ^ 2) ^ (n + 1)) := by
    rw [hg, integral_const_mul, integral_add (integrable_const _) (hSi.const_mul _),
      integral_const_mul, integral_finsetSum _ fun a _ => hXi a]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsum : ∑ a, ∫ ω, (Y a ω ^ 2) ^ (n + 1) ≤ cd * (((N : ℝ) ^ (n + 1))⁻¹ * C') := by
    calc _ ≤ ∑ _a : ι, ((N : ℝ) ^ (n + 1))⁻¹ * C' := Finset.sum_le_sum fun a _ => hXle a
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hM1 : cd ^ n * (cd * (((N : ℝ) ^ (n + 1))⁻¹ * C')) = (cd / N) ^ (n + 1) * C' := by
    rw [div_pow, div_eq_mul_inv]; ring
  have hM2 : (cd / N) ^ (n + 1) ≤ L ^ (n + 1) := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_le_iff₀ hNp, hcd']; exact hcard
  calc ∫ ω, (1 + ∑ a, Y a ω ^ 2) ^ (n + 1) ≤ ∫ ω, g ω := integral_mono hWi hgi hle
    _ ≤ 2 ^ n * (1 + L ^ (n + 1) * C') := by
        rw [hgval]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hcd0 n)
        rw [hM1] at this
        have := mul_le_mul_of_nonneg_right hM2 hC'0
        linarith
    _ ≤ cII_KW L C (n + 1) := by
        unfold cII_KW
        rw [← hC']
        have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h3 : 0 ≤ 1 + L ^ (n + 1) * C' := by positivity
        exact mul_le_mul_of_nonneg_right h2 h3

/-- `E (1 + ‖X‖_F²)^q ≤ 2^q (1 + τ^{−q} N^q C'_{2q})`. -/
private theorem cII_moment_W {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (hN : 1 ≤ N) (hM : (M : ℝ) ≤ τ⁻¹ * N) (q : ℕ) :
    Integrable (fun ω => (1 + cII_sq (X ω)) ^ q) ∧
      ∫ ω, (1 + cII_sq (X ω)) ^ q ≤ cII_KW (τ⁻¹ * N) C q := by
  have hc : (Fintype.card (Fin M × Fin N) : ℝ) ≤ (τ⁻¹ * N) * N := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast
    exact mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)
  have h := cII_moment_family (fun α ω => X ω α.1 α.2) (fun α => hX.measurable α.1 α.2)
    (fun q α => hX.integrable_moment q α.1 α.2) (fun q α => hX.moment q α.1 α.2) hN
    (L := τ⁻¹ * N) (by positivity) hc q
  unfold cII_sq
  exact h

/-- The law of the column `μ` is `colLaw`. -/
private theorem cII_colLaw_eq {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (μ : Fin N) :
    (ℙ : Measure Ω).map (fun ω j => X ω j μ) = colLaw X μ := by
  have hcol : iIndepFun (fun j ω => X ω j μ) ℙ :=
    hX.indep.precomp (g := fun j : Fin M => (j, μ)) fun a b h => (Prod.ext_iff.1 h).1
  exact (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hX.measurable j μ).aemeasurable)).1 hcol

/-- Moments of the column law: `∫ (1 + |y|²)^q d colLaw ≤ 2^q (1 + τ^{−q} C'_{2q})`. -/
private theorem cII_colLaw_moment {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (μ : Fin N) (q : ℕ) :
    Integrable (fun y : Fin M → ℝ => (1 + ∑ j, y j ^ 2) ^ q) (colLaw X μ) ∧
      ∫ y, (1 + ∑ j, y j ^ 2) ^ q ∂(colLaw X μ) ≤ cII_KW τ⁻¹ C q := by
  have hc : (Fintype.card (Fin M) : ℝ) ≤ τ⁻¹ * N := by rw [Fintype.card_fin]; exact hM
  obtain ⟨h1, h2⟩ := cII_moment_family (fun j ω => X ω j μ) (fun j => hX.measurable j μ)
    (fun q j => hX.integrable_moment q j μ) (fun q j => hX.moment q j μ) hN
    (inv_pos.2 hτ).le hc q
  have hYm : Measurable fun ω (j : Fin M) => X ω j μ :=
    measurable_pi_iff.2 fun j => hX.measurable j μ
  have hfm : Measurable fun y : Fin M → ℝ => (1 + ∑ j, y j ^ 2) ^ q :=
    (measurable_const.add (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).pow_const 2)).pow_const _
  rw [← cII_colLaw_eq hX μ]
  refine ⟨(integrable_map_measure hfm.aestronglyMeasurable hYm.aemeasurable).2 h1, ?_⟩
  rw [integral_map hYm.aemeasurable hfm.aestronglyMeasurable]
  exact h2

end Moments

/-! ## Continuity in the matrix -/

section Continuity

variable {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_continuous_G (hSig : Sig.PosDef) (hz : 0 < z.im) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z := by
  have hc : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linH Sig⁻¹ A z := by
    unfold linH cplx
    refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_const
    · exact Continuous.matrix_map continuous_id Complex.continuous_ofReal
    · exact Continuous.matrix_map continuous_id.matrix_transpose Complex.continuous_ofReal
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z) =
      fun A => (linH Sig⁻¹ A z).det⁻¹ • (linH Sig⁻¹ A z).adjugate := by
    funext A
    change (linH Sig⁻¹ A z)⁻¹ = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Continuous.smul ((hc.matrix_det).inv₀ fun A => ?_) hc.matrix_adjugate
  exact ((isUnit_iff_isUnit_det _).1 (H_isUnit hSig A hz)).ne_zero

private theorem cII_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => cII_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

private theorem cII_continuous_updCol (μ : Fin N) :
    Continuous fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin N) ℝ => updCol q.2 μ q.1 := by
  refine continuous_pi fun j => continuous_pi fun ν => ?_
  by_cases h : ν = μ
  · simp only [updCol, h, ite_true]
    exact (continuous_apply j).comp continuous_fst
  · simp only [updCol, h, ite_false]
    exact (continuous_id.matrix_elem j ν).comp continuous_snd

private theorem cII_continuous_updCol0 (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => updCol A μ 0 :=
  (cII_continuous_updCol μ).comp (continuous_const.prodMk continuous_id)

private theorem cII_continuous_entGmu (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N)
    (x y : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y := by
  have h : (fun A : Matrix (Fin M) (Fin N) ℝ => ent (Gmu Sig A z μ) x y) = fun A =>
      ent (G Sig (updCol A μ 0) z) x y + ((x (Sum.inr μ) : ℂ) * (y (Sum.inr μ) : ℂ)) * z⁻¹ :=
    funext fun A => cII_ent_Gmu hSig A hz μ x y
  rw [h]
  exact (((cII_continuous_ent x y).comp (cII_continuous_G hSig hz)).comp
    (cII_continuous_updCol0 μ)).add continuous_const

private theorem cII_continuous_Gmu (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N)
    (s t : Fin M ⊕ Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Gmu Sig A z μ s t := by
  have := cII_continuous_entGmu hSig hz μ (eI s) (eI t)
  simpa only [ent_eI_eI] using this

private theorem cII_continuous_linCol (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N)
    (x : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linForm (colC Sig A z x μ) fun j => A j μ := by
  unfold linForm colC
  exact continuous_finsetSum _ fun j _ => (cII_continuous_entGmu hSig hz μ x _).mul
    (Complex.continuous_ofReal.comp (continuous_id.matrix_elem j μ))

private theorem cII_continuous_linRow (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N)
    (x : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => linForm (rowC Sig A z x μ) fun j => A j μ := by
  unfold linForm rowC
  exact continuous_finsetSum _ fun j _ => (cII_continuous_entGmu hSig hz μ _ x).mul
    (Complex.continuous_ofReal.comp (continuous_id.matrix_elem j μ))

/-- The shape of the list of linear forms of `[G_{xy}]^s` (`true` for a column form). -/
private def cII_bfT (x y : Letter) (s : Fin 3) : List Bool :=
  if s = 0 then []
  else if s = 1 then (if x = .M then [] else [true]) ++ (if y = .M then [] else [false])
  else if x = .V then (if y = .M then [] else [false])
  else if y = .V then (if x = .M then [] else [true]) else []

private theorem cII_brackForms_eq (A : Matrix (Fin M) (Fin N) ℝ) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    brackForms Sig A z v i μ x y s = (cII_bfT x y s).map fun t =>
      if t then colC Sig A z (letVec Sig v i μ x) μ else rowC Sig A z (letVec Sig v i μ y) μ := by
  unfold brackForms cII_bfT
  split_ifs <;> simp

private theorem cII_continuous_brack (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) (x y : Letter) (s : Fin 3) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => brack Sig A z v i μ x y s := by
  unfold brack
  refine Continuous.mul ?_ ?_
  · unfold brackScal
    split_ifs
    · exact cII_continuous_entGmu hSig hz μ _ _
    all_goals exact continuous_const
  · simp only [cII_brackForms_eq, List.map_map]
    refine continuous_list_prod _ fun t _ => ?_
    cases t
    · simpa using cII_continuous_linRow hSig hz μ (letVec Sig v i μ y)
    · simpa using cII_continuous_linCol hSig hz μ (letVec Sig v i μ x)

private theorem cII_continuous_tagA (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => tagA Sig A z v i μ n w σ := by
  cases n with
  | zero =>
    simp only [tagA]
    refine Continuous.mul ?_ ?_
    · unfold emptyScal
      split_ifs
      · exact (cII_continuous_entGmu hSig hz μ _ _).sub continuous_const
      all_goals exact continuous_const
    · unfold emptyForms
      split_ifs
      · exact continuous_const
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        exact (cII_continuous_linCol hSig hz μ _).mul (cII_continuous_linRow hSig hz μ _)
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have e : ∀ A : Matrix (Fin M) (Fin N) ℝ,
            linForm (colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) =
              linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ) +
                linForm (rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) := fun A => by
          simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        simp only [e]
        exact (cII_continuous_linCol hSig hz μ _).add (cII_continuous_linRow hSig hz μ _)
  | succ k =>
    simp only [tagA]
    exact continuous_finsetProd _ fun l _ => cII_continuous_brack hSig hz v i μ _ _ _

private theorem cII_continuous_Ymu (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Ymu Sig A z μ := by
  unfold Ymu
  exact continuous_const.mul (continuous_finsetSum _ fun j _ => cII_continuous_Gmu hSig hz μ _ _)

private theorem cII_continuous_Qmu (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Qmu Sig A z μ := by
  simp only [cII_Qmu_eq]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ =>
    ((Complex.continuous_ofReal.comp (continuous_id.matrix_elem j μ)).mul
      (cII_continuous_Gmu hSig hz μ _ _)).mul
      (Complex.continuous_ofReal.comp (continuous_id.matrix_elem j' μ))

private theorem cII_continuous_P (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N) (K : ℕ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => cII_P Sig A z μ K := by
  have hY := cII_continuous_Ymu hSig hz μ
  have hne : ∀ A : Matrix (Fin M) (Fin N) ℝ, -z - Ymu Sig A z μ ≠ 0 := by
    intro A h
    have := (calY_rough hSig A hz μ).1
    rw [h, Complex.zero_im] at this
    linarith
  have hinv : Continuous fun A : Matrix (Fin M) (Fin N) ℝ => (-z - Ymu Sig A z μ)⁻¹ :=
    (continuous_const.sub hY).inv₀ hne
  unfold cII_P calY
  refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ((cII_continuous_Qmu hSig hz μ).pow _)
  exact continuous_finsetSum _ fun t _ =>
    ((hinv.pow _).mul continuous_const).mul ((continuous_neg.comp hY).pow _)

private theorem cII_continuous_T (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) {g : Matrix (Fin M) (Fin N) ℝ → ℂ}
    (hg : Continuous g) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => cII_T Sig A z v i μ ns ws σs cs (g A) := by
  unfold cII_T
  exact continuous_finsetProd _ fun r _ => (cII_continuous_conjIf (cs r)).comp
    ((cII_continuous_tagA hSig hz v i μ _ _ _).mul (hg.pow _))

private theorem cII_continuous_Gmumu (hSig : Sig.PosDef) (hz : 0 < z.im) (μ : Fin N) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => G Sig A z (Sum.inr μ) (Sum.inr μ) :=
  (cII_continuous_G hSig hz).matrix_elem _ _

private theorem cII_continuous_Fv (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ) :
    Continuous fun A : Matrix (Fin M) (Fin N) ℝ => Fv Sig A z v := by
  unfold Fv
  exact ((cII_continuous_ent _ _).comp ((cII_continuous_G (N := N) hSig hz).sub
    continuous_const)).norm

end Continuity

/-! ## The expansion of `∏_r c_r(P)^{|σ_r|_μ}` in powers of `Q_μ`, `Q̄_μ` -/

section Expansion

/-- The number of `Q` factors (unconjugated) of a multi-index `κ`. -/
private def cII_k1 {p : ℕ} {t : Fin p → ℕ} (cs : Fin p → Bool) {K : ℕ}
    (κ : (Σ r, Fin (t r)) → Fin (K + 1)) : ℕ :=
  ∑ a, if cs a.1 then 0 else (κ a : ℕ)

/-- The number of `Q̄` factors of a multi-index `κ`. -/
private def cII_k2 {p : ℕ} {t : Fin p → ℕ} (cs : Fin p → Bool) {K : ℕ}
    (κ : (Σ r, Fin (t r)) → Fin (K + 1)) : ℕ :=
  ∑ a, if cs a.1 then (κ a : ℕ) else 0

/-- `Q^{k₁} Q̄^{k₂} = ∏_{u < k₁ + k₂} c_u(Q)` with `c_u = conj` for `u ≥ k₁`. -/
private theorem cII_prod_conjIf_add (k₁ k₂ : ℕ) (g : ℂ) :
    ∏ u : Fin (k₁ + k₂), conjIf (decide (k₁ ≤ (u : ℕ))) g = g ^ k₁ * conjIf true g ^ k₂ := by
  rw [Fin.prod_univ_add]
  have e1 : ∀ u : Fin k₁,
      conjIf (decide (k₁ ≤ ((Fin.castAdd k₂ u : Fin (k₁ + k₂)) : ℕ))) g = g := by
    intro u
    have h : ¬ k₁ ≤ ((Fin.castAdd k₂ u : Fin (k₁ + k₂)) : ℕ) := by
      simp only [Fin.val_castAdd, not_le]; exact u.2
    simp only [h, decide_false]; rfl
  have e2 : ∀ u : Fin k₂, conjIf (decide (k₁ ≤ ((Fin.natAdd k₁ u : Fin (k₁ + k₂)) : ℕ))) g =
      conjIf true g := by
    intro u
    have h : k₁ ≤ ((Fin.natAdd k₁ u : Fin (k₁ + k₂)) : ℕ) := by
      simp only [Fin.val_natAdd]; omega
    simp only [h, decide_true]
  rw [Finset.prod_congr rfl fun u _ => e1 u, Finset.prod_congr rfl fun u _ => e2 u]
  simp

private theorem cII_prod_conjIf_pow {ι : Type*} [Fintype ι] (b : ι → Bool) (e : ι → ℕ) (g : ℂ) :
    ∏ a, conjIf (b a) g ^ e a =
      g ^ (∑ a, if b a then 0 else e a) * conjIf true g ^ (∑ a, if b a then e a else 0) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  cases h : b a <;> simp [conjIf]

/-- `∏_r c_r(∑_{k ≤ K} 𝒴_k Q^k)^{t_r} = ∑_κ (∏_a c(𝒴_{κ a})) ∏_{u} c_u(Q)`. -/
private theorem cII_expand {p : ℕ} (t : Fin p → ℕ) (cs : Fin p → Bool) (K : ℕ) (Yc : ℕ → ℂ)
    (g : ℂ) :
    ∏ r, conjIf (cs r) (∑ k ∈ Finset.range (K + 1), Yc k * g ^ k) ^ t r =
      ∑ κ : (Σ r, Fin (t r)) → Fin (K + 1), (∏ a, conjIf (cs a.1) (Yc (κ a))) *
        ∏ u : Fin (cII_k1 cs κ + cII_k2 cs κ), conjIf (decide (cII_k1 cs κ ≤ (u : ℕ))) g := by
  have h1 : ∀ r, conjIf (cs r) (∑ k ∈ Finset.range (K + 1), Yc k * g ^ k) ^ t r =
      ∏ _l : Fin (t r), ∑ k : Fin (K + 1), conjIf (cs r) (Yc k) * conjIf (cs r) g ^ (k : ℕ) := by
    intro r
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, cII_conjIf_sum,
      ← Fin.sum_univ_eq_sum_range]
    simp only [cII_conjIf_mul, cII_conjIf_pow]
  simp only [h1]
  rw [← Fintype.prod_sigma (fun a : (Σ r, Fin (t r)) =>
    ∑ k : Fin (K + 1), conjIf (cs a.1) (Yc k) * conjIf (cs a.1) g ^ (k : ℕ)), Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib, cII_prod_conjIf_add, cII_prod_conjIf_pow]
  rfl

end Expansion

/-! ## The integrand at the column `y` -/

section Column

variable {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_col_updCol (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (y : Fin M → ℝ) :
    (fun j => updCol A μ y j μ) = y := funext fun j => by simp [updCol]

private theorem cII_Ymu_updCol (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) (y : Fin M → ℝ) :
    Ymu Sig (updCol A μ y) z μ = Ymu Sig A z μ := by
  unfold Ymu; rw [Gmu_updCol]

/-- `A(w, σ)` at the column `y`: `A⁰(w, σ) A⁺(w, σ)(y)`. -/
private theorem cII_tagA_updCol (A : Matrix (Fin M) (Fin N) ℝ) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) (y : Fin M → ℝ) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    tagA Sig (updCol A μ y) z v i μ n w σ = tagScal Sig A z v i μ n w σ *
      ((tagForms Sig A z v i μ n w σ).map fun c => linForm c y).prod := by
  rw [tagA_eq_scal_mul, (tagScal_updCol Sig A z v i μ y n w σ).1,
    (tagScal_updCol Sig A z v i μ y n w σ).2, cII_col_updCol]

/-- The integrand at `P_μ` in place of `G_μμ`, at the column `y`, expanded in `Q_μ(y)`. -/
private theorem cII_TP_updCol (A : Matrix (Fin M) (Fin N) ℝ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (K : ℕ) (y : Fin M → ℝ) :
    cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ K) =
      (∏ r, conjIf (cs r) (tagScal Sig A z v i μ (ns r) (ws r) (σs r))) *
        ∑ κ : (Σ r, Fin (tagMu (σs r))) → Fin (K + 1),
          (∏ a, conjIf (cs a.1) (calY z (Ymu Sig A z μ) K (κ a))) *
            ((∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
                fun c => linForm c y).prod)) *
              ∏ u : Fin (cII_k1 cs κ + cII_k2 cs κ),
                conjIf (decide (cII_k1 cs κ ≤ (u : ℕ))) (Qmu Sig (updCol A μ y) z μ)) := by
  unfold cII_T cII_P
  simp only [cII_tagA_updCol, cII_Ymu_updCol, cII_conjIf_mul, cII_conjIf_pow,
    Finset.prod_mul_distrib]
  have h := cII_expand (fun r => tagMu (σs r)) cs K (fun k => calY z (Ymu Sig A z μ) K k)
    (Qmu Sig (updCol A μ y) z μ)
  rw [h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

end Column

/-! ## Polynomial growth in the column and integrability against `colLaw` -/

section Growth

/-- `W(y) = 1 + |y|²`. -/
private def cII_W (y : Fin M → ℝ) : ℝ := 1 + ∑ j, y j ^ 2

private theorem cII_W_one (y : Fin M → ℝ) : 1 ≤ cII_W y := by
  unfold cII_W
  have : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem cII_abs_le_W (y : Fin M → ℝ) (j : Fin M) : |y j| ≤ cII_W y := by
  unfold cII_W
  have h1 : y j ^ 2 ≤ ∑ j, y j ^ 2 :=
    Finset.single_le_sum (f := fun j => y j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [abs_nonneg (y j), sq_abs (y j)]

/-- Polynomial growth `|f(y)| ≤ a W(y)^n`. -/
private def cII_PG (f : (Fin M → ℝ) → ℂ) : Prop :=
  ∃ a : ℝ, ∃ n : ℕ, 0 ≤ a ∧ ∀ y, ‖f y‖ ≤ a * cII_W y ^ n

private theorem cII_PG_const (b : ℂ) : cII_PG (M := M) fun _ => b :=
  ⟨‖b‖, 0, norm_nonneg _, fun y => by simp⟩

private theorem cII_PG_mul {f g : (Fin M → ℝ) → ℂ} (hf : cII_PG f) (hg : cII_PG g) :
    cII_PG fun y => f y * g y := by
  obtain ⟨a, n, ha, hf⟩ := hf
  obtain ⟨b, m, hb, hg⟩ := hg
  refine ⟨a * b, n + m, mul_nonneg ha hb, fun y => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖f y‖ * ‖g y‖ ≤ (a * cII_W y ^ n) * (b * cII_W y ^ m) :=
        mul_le_mul (hf y) (hg y) (norm_nonneg _) (by have := cII_W_one y; positivity)
    _ = _ := by ring

private theorem cII_PG_prod {ι : Type*} (s : Finset ι) {f : ι → (Fin M → ℝ) → ℂ}
    (hf : ∀ i ∈ s, cII_PG (f i)) : cII_PG fun y => ∏ i ∈ s, f i y := by
  induction s using Finset.induction_on with
  | empty => simpa using cII_PG_const (M := M) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact cII_PG_mul (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem cII_PG_list {α : Type*} (l : List α) {f : α → (Fin M → ℝ) → ℂ}
    (hf : ∀ c ∈ l, cII_PG (f c)) : cII_PG fun y => (l.map fun c => f c y).prod := by
  induction l with
  | nil => simpa using cII_PG_const (M := M) 1
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact cII_PG_mul (hf a (List.mem_cons_self ..))
      (ih fun c hc => hf c (List.mem_cons_of_mem _ hc))

private theorem cII_PG_conjIf (b : Bool) {f : (Fin M → ℝ) → ℂ} (hf : cII_PG f) :
    cII_PG fun y => conjIf b (f y) := by
  obtain ⟨a, n, ha, hf⟩ := hf
  exact ⟨a, n, ha, fun y => by rw [cII_norm_conjIf]; exact hf y⟩

private theorem cII_PG_linForm (cv : Fin M → ℂ) : cII_PG fun y => linForm cv y := by
  refine ⟨∑ j, ‖cv j‖, 1, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun y => ?_⟩
  unfold linForm
  refine (norm_sum_le _ _).trans ?_
  rw [pow_one, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (cII_abs_le_W y j) (norm_nonneg _)

private theorem cII_PG_quad (B : Fin M → Fin M → ℂ) :
    cII_PG fun y => ∑ j, ∑ j', (y j : ℂ) * B j j' * (y j' : ℂ) := by
  refine ⟨∑ j, ∑ j', ‖B j j'‖, 2,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, fun y => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j' _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 := cII_abs_le_W y j
  have h2 := cII_abs_le_W y j'
  have h0 := abs_nonneg (y j)
  have h0' := abs_nonneg (y j')
  have hB := norm_nonneg (B j j')
  calc |y j| * ‖B j j'‖ * |y j'| = ‖B j j'‖ * (|y j| * |y j'|) := by ring
    _ ≤ ‖B j j'‖ * (cII_W y * cII_W y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 h0' (by linarith)) hB
    _ = ‖B j j'‖ * cII_W y ^ 2 := by ring

private theorem cII_integrable_PG {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {τ : ℝ} (hτ : 0 < τ) {C : ℕ → ℝ}
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (μ : Fin N) {f : (Fin M → ℝ) → ℂ} (hc : Continuous f)
    (hf : cII_PG f) : Integrable f (colLaw X μ) := by
  obtain ⟨a, n, ha, hf⟩ := hf
  have h := (cII_colLaw_moment hτ hX hN hM μ n).1
  refine (h.const_mul a).mono' hc.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  exact hf y

/-- The integrand of Lemma 8.11 has polynomial growth and is continuous in the column. -/
private theorem cII_lem87_integrand {Sig : Matrix (Fin M) (Fin M) ℝ}
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M) (μ : Fin N)
    {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) {k : ℕ} (ct : Fin k → Bool) :
    Continuous (fun y : Fin M → ℝ => (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r)
        (σs r)).map fun c => linForm c y).prod)) *
          ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)) ∧
      cII_PG (fun y : Fin M → ℝ => (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r)
        (σs r)).map fun c => linForm c y).prod)) *
          ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)) := by
  have hlin : ∀ cv : Fin M → ℂ, Continuous fun y : Fin M → ℝ => linForm cv y := fun cv => by
    unfold linForm
    exact continuous_finsetSum _ fun j _ => continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_apply j))
  refine ⟨?_, ?_⟩
  · refine Continuous.mul ?_ ?_
    · exact continuous_finsetProd _ fun r _ => (cII_continuous_conjIf (cs r)).comp
        (continuous_list_prod _ fun cv _ => hlin cv)
    · simp only [Qmu_updCol]
      exact continuous_finsetProd _ fun t _ => (cII_continuous_conjIf (ct t)).comp
        (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ =>
          ((Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const).mul
            (Complex.continuous_ofReal.comp (continuous_apply j')))
  · refine cII_PG_mul ?_ ?_
    · exact cII_PG_prod _ fun r _ => cII_PG_conjIf _ (cII_PG_list _ fun cv _ => cII_PG_linForm cv)
    · simp only [Qmu_updCol]
      exact cII_PG_prod _ fun t _ => cII_PG_conjIf _ (cII_PG_quad _)

end Growth

/-! ## The conditional expectation in the column `μ` (sec8 3) -/

section CondExp

variable {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_card_sigma {p : ℕ} {ns : Fin p → ℕ} (σs : ∀ r, Fin (ns r + 1) → Fin 3) :
    Fintype.card (Σ r, Fin (tagMu (σs r))) = dMuof σs := by
  rw [Fintype.card_sigma]; simp [dMuof]

private theorem cII_k12_le {p : ℕ} {t : Fin p → ℕ} (cs : Fin p → Bool) {K : ℕ}
    (κ : (Σ r, Fin (t r)) → Fin (K + 1)) :
    cII_k1 cs κ + cII_k2 cs κ ≤ K * Fintype.card (Σ r, Fin (t r)) := by
  unfold cII_k1 cII_k2
  rw [← Finset.sum_add_distrib]
  calc ∑ a, ((if cs a.1 then 0 else (κ a : ℕ)) + if cs a.1 then (κ a : ℕ) else 0)
      ≤ ∑ _a : (Σ r, Fin (t r)), K := Finset.sum_le_sum fun a _ => by
        have := (κ a).2
        split_ifs <;> omega
    _ = K * Fintype.card (Σ r, Fin (t r)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- The column average of the truncated integrand: on `|Y_μ|, |(−z−Y_μ)⁻¹| ≤ 2K`, a bound `B`
of Lemma 8.11 for each monomial `Q^{k₁} Q̄^{k₂}` (`k₁ + k₂ ≤ K_τ d_μ`) gives
`|E_μ ∏_r c_r(A(w_r, σ_r) P^{|σ_r|_μ})| ≤ ∏_r |A⁰_r| ((K_τ+1)² 2^{K_τ} (2K)^{2K_τ+1})^{d_μ} B`. -/
private theorem cII_g_le (A : Matrix (Fin M) (Fin N) ℝ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (Kt : ℕ) (ν : Measure (Fin M → ℝ))
    {K Bd : ℝ} (hK : 1 ≤ K) (hY : ‖Ymu Sig A z μ‖ ≤ 2 * K)
    (hw : ‖(-z - Ymu Sig A z μ)⁻¹‖ ≤ 2 * K)
    (hint : ∀ (k : ℕ) (ct : Fin k → Bool), Integrable (fun y : Fin M → ℝ =>
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)) ν)
    (hL : ∀ (k : ℕ) (ct : Fin k → Bool), k ≤ Kt * dMuof σs → ‖∫ y,
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) ∂ν‖ ≤ Bd) :
    ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt) ∂ν‖ ≤
      (∏ r, ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖) *
        (((Kt + 1) * ((Kt + 1) * 2 ^ Kt * (2 * K) ^ (2 * Kt + 1))) ^ dMuof σs * Bd) := by
  set F : (Fin M → ℝ) → ℂ := fun y => ∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r)
    (σs r)).map fun c => linForm c y).prod) with hFdef
  obtain ⟨cY, hcY⟩ : ∃ cY : ℝ, cY = (Kt + 1) * 2 ^ Kt * (2 * K) ^ (2 * Kt + 1) := ⟨_, rfl⟩
  rw [← hcY]
  have hcY0 : 0 ≤ cY := by rw [hcY]; have : (0 : ℝ) ≤ K := by linarith
                           positivity
  have hBd : 0 ≤ Bd := (norm_nonneg _).trans (hL 0 (fun t => Fin.elim0 t) (Nat.zero_le _))
  have hcoef : ∀ κ : (Σ r, Fin (tagMu (σs r))) → Fin (Kt + 1),
      ‖∏ a, conjIf (cs a.1) (calY z (Ymu Sig A z μ) Kt (κ a))‖ ≤ cY ^ dMuof σs := by
    intro κ
    rw [norm_prod]
    calc ∏ a, ‖conjIf (cs a.1) (calY z (Ymu Sig A z μ) Kt (κ a))‖ ≤
          ∏ _a : (Σ r, Fin (tagMu (σs r))), cY :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun a _ => by
            rw [cII_norm_conjIf, hcY]
            exact cII_calY_le (by linarith) hY hw Kt _
      _ = cY ^ dMuof σs := by rw [Finset.prod_const, Finset.card_univ, cII_card_sigma]
  have hexp : (fun y => cII_T Sig (updCol A μ y) z v i μ ns ws σs cs
      (cII_P Sig (updCol A μ y) z μ Kt)) = fun y =>
      (∏ r, conjIf (cs r) (tagScal Sig A z v i μ (ns r) (ws r) (σs r))) *
        ∑ κ : (Σ r, Fin (tagMu (σs r))) → Fin (Kt + 1),
          (∏ a, conjIf (cs a.1) (calY z (Ymu Sig A z μ) Kt (κ a))) *
            (F y * ∏ u : Fin (cII_k1 cs κ + cII_k2 cs κ),
                conjIf (decide (cII_k1 cs κ ≤ (u : ℕ))) (Qmu Sig (updCol A μ y) z μ)) :=
    funext fun y => cII_TP_updCol A v i μ ns ws σs cs Kt y
  rw [hexp, integral_const_mul, integral_finsetSum _ fun κ _ => (hint _ _).const_mul _]
  simp only [integral_const_mul]
  rw [norm_mul, norm_prod]
  simp only [cII_norm_conjIf]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ κ : (Σ r, Fin (tagMu (σs r))) → Fin (Kt + 1),
        ‖(∏ a, conjIf (cs a.1) (calY z (Ymu Sig A z μ) Kt (κ a))) *
          ∫ y, F y * ∏ u : Fin (cII_k1 cs κ + cII_k2 cs κ),
            conjIf (decide (cII_k1 cs κ ≤ (u : ℕ))) (Qmu Sig (updCol A μ y) z μ) ∂ν‖
      ≤ ∑ _κ : (Σ r, Fin (tagMu (σs r))) → Fin (Kt + 1), cY ^ dMuof σs * Bd := by
        refine Finset.sum_le_sum fun κ _ => ?_
        rw [norm_mul]
        refine mul_le_mul (hcoef κ) (hL _ _ ?_) (norm_nonneg _) (by positivity)
        have := cII_k12_le cs κ
        rwa [cII_card_sigma] at this
    _ = ((Kt + 1) * cY) ^ dMuof σs * Bd := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          cII_card_sigma, nsmul_eq_mul, mul_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        ring

end CondExp

/-! ## The scalar parts of the nonempty words and their sum over `i` (818) -/

section Scalars

variable {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_Gmu_col_zero (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N)
    (x : Fin M ⊕ Fin N → ℝ) : ent (Gmu Sig A z μ) x (eI (Sum.inr μ)) = 0 := by
  rw [cII_ent_eI_right]; simp [Gmu, G1, Gm]

private theorem cII_Gmu_row_zero (A : Matrix (Fin M) (Fin N) ℝ) (μ : Fin N)
    (y : Fin M ⊕ Fin N → ℝ) : ent (Gmu Sig A z μ) (eI (Sum.inr μ)) y = 0 := by
  rw [cII_ent_eI_left]; simp [Gmu, G1, Gm]

/-- The endpoint value `u_i = |G^{(μ)}_{v̄ i}| + |G^{(μ)}_{i v̄}|`. -/
private def cII_u (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (i : Fin M) : ℝ :=
  ‖colC Sig A z (vbar Sig v) μ i‖ + ‖rowC Sig A z (vbar Sig v) μ i‖

/-- On `GoodMinor`, `|[G_{xy}]^s|` (scalar part) is at most `u_i` for the endpoint factors
`[G_{v̄i}]^0`, `[G_{iv̄}]^0`, and at most `K` otherwise. -/
private theorem cII_brackScal_good {K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (h : GoodMinor K b Sig A z v μ) (i : Fin M)
    (x y : Letter) (hxy : ¬(x = .V ∧ y = .V)) (s : Fin 3) :
    ‖brackScal Sig A z v i μ x y s‖ ≤
      if s = 0 ∧ ((x = .V ∧ y = .I) ∨ (x = .I ∧ y = .V)) then cII_u Sig A z v μ i else K := by
  have hu1 : ‖ent (Gmu Sig A z μ) (vbar Sig v) (eI (Sum.inl i))‖ ≤ cII_u Sig A z v μ i :=
    le_add_of_nonneg_right (norm_nonneg _)
  have hu2 : ‖ent (Gmu Sig A z μ) (eI (Sum.inl i)) (vbar Sig v)‖ ≤ cII_u Sig A z v μ i :=
    le_add_of_nonneg_left (norm_nonneg _)
  have hK0 : (0 : ℝ) ≤ K := by linarith
  cases x <;> cases y
  · exact absurd ⟨rfl, rfl⟩ hxy
  all_goals fin_cases s
  all_goals first
    | (simp [brackScal, letVec, cII_Gmu_col_zero, cII_Gmu_row_zero, hK0, hK]; done)
    | simpa [brackScal, letVec, cII_Gmu_col_zero, cII_Gmu_row_zero, hK0, hK] using hu1
    | simpa [brackScal, letVec, cII_Gmu_col_zero, cII_Gmu_row_zero, hK0, hK] using hu2
    | simpa [brackScal, letVec, cII_Gmu_col_zero, cII_Gmu_row_zero, hK0, hK, ent_eI_eI]
        using h.ent_jk i i

end Scalars

section Scalars2

variable {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_bs_first {K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (h : GoodMinor K b Sig A z v μ) (i : Fin M)
    (b' : Bool) (s : Fin 3) :
    ‖brackScal Sig A z v i μ .V (Letter.ofT b') s‖ ≤
      if s = 0 ∧ Letter.ofT b' = .I then cII_u Sig A z v μ i else K := by
  have h1 := cII_brackScal_good hK h i .V (Letter.ofT b') (fun h' => cII_ofT_ne b' h'.2) s
  by_cases c2 : s = 0 ∧ Letter.ofT b' = .I
  · have c1 : s = 0 ∧ ((Letter.V = Letter.V ∧ Letter.ofT b' = .I) ∨
        (Letter.V = Letter.I ∧ Letter.ofT b' = .V)) := ⟨c2.1, Or.inl ⟨rfl, c2.2⟩⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true c1)] at h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true c2)]
    exact h1
  · have c1 : ¬ (s = 0 ∧ ((Letter.V = Letter.V ∧ Letter.ofT b' = .I) ∨
        (Letter.V = Letter.I ∧ Letter.ofT b' = .V))) := fun c => c2 ⟨c.1, c.2.elim
          (fun h' => h'.2) (fun h' => absurd h'.1 (by decide))⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false c1)] at h1
    rw [ite_eq_right_of_eq_false _ _ (eq_false c2)]
    exact h1

private theorem cII_bs_last {K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (h : GoodMinor K b Sig A z v μ) (i : Fin M)
    (b' : Bool) (s : Fin 3) :
    ‖brackScal Sig A z v i μ (Letter.ofS b') .V s‖ ≤
      if s = 0 ∧ Letter.ofS b' = .I then cII_u Sig A z v μ i else K := by
  have h1 := cII_brackScal_good hK h i (Letter.ofS b') .V (fun h' => cII_ofS_ne b' h'.1) s
  by_cases c2 : s = 0 ∧ Letter.ofS b' = .I
  · have c1 : s = 0 ∧ ((Letter.ofS b' = Letter.V ∧ Letter.V = .I) ∨
        (Letter.ofS b' = Letter.I ∧ Letter.V = .V)) := ⟨c2.1, Or.inr ⟨c2.2, rfl⟩⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true c1)] at h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true c2)]
    exact h1
  · have c1 : ¬ (s = 0 ∧ ((Letter.ofS b' = Letter.V ∧ Letter.V = .I) ∨
        (Letter.ofS b' = Letter.I ∧ Letter.V = .V))) := fun c => c2 ⟨c.1, c.2.elim
          (fun h' => absurd h'.2 (by decide)) (fun h' => h'.1)⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false c1)] at h1
    rw [ite_eq_right_of_eq_false _ _ (eq_false c2)]
    exact h1

private theorem cII_bs_mid {K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (h : GoodMinor K b Sig A z v μ) (i : Fin M)
    (x y : Letter) (hx : x ≠ .V) (hy : y ≠ .V) (s : Fin 3) :
    ‖brackScal Sig A z v i μ x y s‖ ≤ K := by
  have h1 := cII_brackScal_good hK h i x y (fun h' => hx h'.1) s
  split_ifs at h1 with c1
  · exfalso; rcases c1 with ⟨-, ⟨hx', -⟩ | ⟨-, hy'⟩⟩
    · exact hx hx'
    · exact hy hy'
  · exact h1

private theorem cII_three_le {a m c u K : ℝ} {k : ℕ} (P Q : Prop) [Decidable P] [Decidable Q]
    (hK : 1 ≤ K) (hu : 0 ≤ u) (hm0 : 0 ≤ m) (hc0 : 0 ≤ c)
    (ha : a ≤ if P then u else K) (hm : m ≤ K ^ k) (hc : c ≤ if Q then u else K) :
    a * m * c ≤ K ^ (k + 1 + 1) * u ^ ((if P then 1 else 0) + (if Q then 1 else 0)) := by
  have hK0 : 0 ≤ K := by linarith
  have hk1 : K ^ k ≤ K ^ (k + 1) := pow_le_pow_right₀ hK (by omega)
  have hk2 : K ^ (k + 1) ≤ K ^ (k + 1 + 1) := pow_le_pow_right₀ hK (by omega)
  have hpk : 0 ≤ K ^ k := by positivity
  split_ifs at ha hc ⊢
  · calc a * m * c ≤ u * K ^ k * u := mul_le_mul (mul_le_mul ha hm hm0 hu) hc hc0 (by positivity)
      _ = K ^ k * u ^ 2 := by ring
      _ ≤ K ^ (k + 1 + 1) * u ^ 2 := mul_le_mul_of_nonneg_right (hk1.trans hk2) (sq_nonneg u)
      _ = K ^ (k + 1 + 1) * u ^ (1 + 1) := by norm_num
  · calc a * m * c ≤ u * K ^ k * K := mul_le_mul (mul_le_mul ha hm hm0 hu) hc hc0 (by positivity)
      _ ≤ K ^ (k + 1 + 1) * u ^ (1 + 0) := by
          rw [pow_succ K (k + 1), pow_succ K k]
          have : u * K ^ k * K = K ^ k * K * u := by ring
          rw [this]
          have h2 : K ^ k * K * u ≤ K ^ k * K * K * u := by
            have : K ^ k * K ≤ K ^ k * K * K := le_mul_of_one_le_right (by positivity) hK
            exact mul_le_mul_of_nonneg_right this hu
          simpa using h2
  · calc a * m * c ≤ K * K ^ k * u := mul_le_mul (mul_le_mul ha hm hm0 hK0) hc hc0 (by positivity)
      _ ≤ K ^ (k + 1 + 1) * u ^ (0 + 1) := by
          rw [pow_succ K (k + 1), pow_succ K k]
          have : K * K ^ k * u = K ^ k * K * u := by ring
          rw [this]
          have h2 : K ^ k * K * u ≤ K ^ k * K * K * u := by
            have : K ^ k * K ≤ K ^ k * K * K := le_mul_of_one_le_right (by positivity) hK
            exact mul_le_mul_of_nonneg_right this hu
          simpa using h2
  · calc a * m * c ≤ K * K ^ k * K := mul_le_mul (mul_le_mul ha hm hm0 hK0) hc hc0 (by positivity)
      _ = K ^ (k + 1 + 1) * u ^ (0 + 0) := by ring

/-- For a nonempty word, `|A⁰(w, σ)| ≤ K^{n(w)+1} u_i^{f_i(w, σ)}` on `GoodMinor`. -/
private theorem cII_tagScal_le {K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (h : GoodMinor K b Sig A z v μ) (i : Fin M)
    (k : ℕ) (w : Word (k + 1)) (σ : Fin (k + 1 + 1) → Fin 3) :
    ‖tagScal Sig A z v i μ (k + 1) w σ‖ ≤
      K ^ (k + 1 + 1) * cII_u Sig A z v μ i ^ tagF (k + 1) w σ := by
  have hu0 : 0 ≤ cII_u Sig A z v μ i := by unfold cII_u; positivity
  simp only [tagScal, tagF]
  rw [norm_prod, Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  have hx0 : factorX w 0 = .V := by simp [factorX]
  have hy0 : factorY w 0 = Letter.ofT (w 0) := by simp [factorY]
  have hxl : factorX w (Fin.last k).succ = Letter.ofS (w (Fin.last k)) := by
    simp [factorX]; try rfl
  have hyl : factorY w (Fin.last k).succ = .V := by simp [factorY]
  have hlast : (Fin.last (k + 1) : Fin (k + 1 + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
  rw [hlast, hx0, hy0, hxl, hyl]
  have hmid : ∏ j : Fin k, ‖brackScal Sig A z v i μ (factorX w j.castSucc.succ)
      (factorY w j.castSucc.succ) (σ j.castSucc.succ)‖ ≤ K ^ k := by
    calc _ ≤ ∏ _j : Fin k, K := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => by
          have hx : factorX w j.castSucc.succ ≠ .V := by
            simp only [factorX]; split_ifs with h1
            · simp at h1
            · exact cII_ofS_ne _
          have hy : factorY w j.castSucc.succ ≠ .V := by
            simp only [factorY]; split_ifs with h1
            · exact cII_ofT_ne _
            · simp at h1
          exact cII_bs_mid hK h i _ _ hx hy _
      _ = K ^ k := by simp
  rw [← mul_assoc]
  exact cII_three_le _ _ hK hu0 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (norm_nonneg _) (cII_bs_first hK h i (w 0) (σ 0)) hmid
    (cII_bs_last hK h i (w (Fin.last k)) (σ (Fin.last k).succ))

/-- `∑_i u_i^f ≤ 4 τ⁻¹ N (2K)^f b^{f ∧ 2}` on `GoodMinor` (bound_sum_hat). -/
private theorem cII_sum_u_le {τ K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hK : 1 ≤ K) (hb : 0 ≤ b)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) (h : GoodMinor K b Sig A z v μ) (f : ℕ) :
    ∑ i, cII_u Sig A z v μ i ^ f ≤ 4 * τ⁻¹ * N * (2 * K) ^ f * b ^ (min f 2) := by
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hc := fun j => (h.ent_vj j).1
  have hr := fun j => (h.ent_vj j).2
  have hc2 := h.ward_v.1
  have hr2 := h.ward_v.2
  have h2K : 1 ≤ 2 * K := by linarith
  have hu0 : ∀ i, 0 ≤ cII_u Sig A z v μ i := fun i => by unfold cII_u; positivity
  rcases f with _ | _ | f
  · simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Nat.zero_le, min_eq_left]
    nlinarith
  · simp only [zero_add, pow_one]
    have h1 := bound_sum_hat hτ hτ1 hK hb hM _ hc hc2 1
    have h2 := bound_sum_hat hτ hτ1 hK hb hM _ hr hr2 1
    simp only [pow_one, Nat.reduceSub, pow_zero, mul_one, show min 1 2 = 1 from rfl] at h1 h2 ⊢
    unfold cII_u
    rw [Finset.sum_add_distrib]
    have : 0 ≤ τ⁻¹ * N * b := by positivity
    nlinarith
  · have hmin : min (f + 1 + 1) 2 = 2 := by omega
    rw [hmin]
    have hpt : ∀ i, cII_u Sig A z v μ i ^ (f + 1 + 1) ≤
        (2 * K) ^ f * (2 * (‖colC Sig A z (vbar Sig v) μ i‖ ^ 2 +
          ‖rowC Sig A z (vbar Sig v) μ i‖ ^ 2)) := by
      intro i
      have hui : cII_u Sig A z v μ i ≤ 2 * K := by
        unfold cII_u; linarith [hc i, hr i]
      have hs : cII_u Sig A z v μ i ^ 2 ≤ 2 * (‖colC Sig A z (vbar Sig v) μ i‖ ^ 2 +
          ‖rowC Sig A z (vbar Sig v) μ i‖ ^ 2) := by
        unfold cII_u
        nlinarith [sq_nonneg (‖colC Sig A z (vbar Sig v) μ i‖ - ‖rowC Sig A z (vbar Sig v) μ i‖)]
      have hp : cII_u Sig A z v μ i ^ f ≤ (2 * K) ^ f := pow_le_pow_left₀ (hu0 i) hui f
      have e : cII_u Sig A z v μ i ^ (f + 1 + 1) =
          cII_u Sig A z v μ i ^ f * cII_u Sig A z v μ i ^ 2 := by
        ring
      rw [e]
      exact mul_le_mul hp hs (sq_nonneg _) (by positivity)
    calc ∑ i, cII_u Sig A z v μ i ^ (f + 1 + 1)
        ≤ ∑ i, (2 * K) ^ f * (2 * (‖colC Sig A z (vbar Sig v) μ i‖ ^ 2 +
          ‖rowC Sig A z (vbar Sig v) μ i‖ ^ 2)) := Finset.sum_le_sum fun i _ => hpt i
      _ = (2 * K) ^ f * (2 * (∑ i, ‖colC Sig A z (vbar Sig v) μ i‖ ^ 2 +
          ∑ i, ‖rowC Sig A z (vbar Sig v) μ i‖ ^ 2)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (2 * K) ^ f * (2 * (N * b ^ 2 + N * b ^ 2)) := by gcongr
      _ ≤ 4 * τ⁻¹ * N * (2 * K) ^ (f + 1 + 1) * b ^ 2 := by
          have h4 : (2 * K) ^ f ≤ (2 * K) ^ (f + 1 + 1) := pow_le_pow_right₀ h2K (by omega)
          have h5 : 0 ≤ (N : ℝ) * b ^ 2 := by positivity
          have h6 : 0 ≤ (2 * K) ^ f := by positivity
          nlinarith [mul_le_mul_of_nonneg_right h4 h5, mul_le_mul_of_nonneg_left hT
            (mul_nonneg (by positivity : (0:ℝ) ≤ (2 * K) ^ (f + 1 + 1)) h5)]

end Scalars2

/-! ## Empty words, the split into nonempty and empty words -/

section Words

variable {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_tagMu_zero (n : ℕ) (σ : Fin (n + 1) → Fin 3) (hn : n = 0) :
    tagMu σ = if σ 0 = 0 then 0 else 1 := by
  subst hn
  simp [tagMu]

private theorem cII_tagF_zero (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hn : n = 0) :
    tagF n w σ = 0 := by
  subst hn; rfl

private theorem cII_tagF_le (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) :
    tagF n w σ ≤ 2 * n := by
  cases n with
  | zero => simp [tagF]
  | succ k => simp only [tagF]; split_ifs <;> omega

/-- `A(w₀, σ)` for the empty word: the scalar `A⁰` and, for `σ ≠ 0`, `|A| ≤ 2b` on `Θ`. -/
private theorem cII_empty_tagA {τ K b Cn : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h : GoodSec8 τ K b Cn Sig A z v μ)
    (i : Fin M) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hn : n = 0) (hσ : σ 0 ≠ 0) :
    ‖tagA Sig A z v i μ n w σ‖ ≤ 2 * b := by
  subst hn
  have hcV := h.col_v.1
  have hrV := h.col_v.2
  generalize hs : σ 0 = s at hσ
  simp only [tagA, hs]
  fin_cases s
  · exact absurd rfl hσ
  · simp only [emptyForms, emptyScal, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, norm_mul]
    have : ‖linForm (colC Sig A z (vbar Sig v) μ) fun j => A j μ‖ *
        ‖linForm (rowC Sig A z (vbar Sig v) μ) fun j => A j μ‖ ≤ b * b :=
      mul_le_mul hcV hrV (norm_nonneg _) hb0
    nlinarith
  · simp only [emptyForms, emptyScal, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, neg_mul, one_mul,
      norm_neg]
    have e : linForm (colC Sig A z (vbar Sig v) μ + rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) =
        linForm (colC Sig A z (vbar Sig v) μ) (fun j => A j μ) +
          linForm (rowC Sig A z (vbar Sig v) μ) (fun j => A j μ) := by
      simp only [linForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e]
    have := norm_add_le (linForm (colC Sig A z (vbar Sig v) μ) fun j => A j μ)
      (linForm (rowC Sig A z (vbar Sig v) μ) fun j => A j μ)
    linarith

private theorem cII_empty_scal_one {A : Matrix (Fin M) (Fin N) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    {μ : Fin N} (i : Fin M) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hn : n = 0)
    (hσ : σ 0 ≠ 0) : ‖tagScal Sig A z v i μ n w σ‖ = 1 := by
  subst hn
  simp only [tagScal, emptyScal, hσ, ↓reduceIte]
  split_ifs <;> simp

private theorem cII_empty_scal_zero {A : Matrix (Fin M) (Fin N) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    {μ : Fin N} (i : Fin M) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hn : n = 0)
    (hσ : σ 0 = 0) : tagScal Sig A z v i μ n w σ = tagA Sig A z v i μ n w σ := by
  subst hn
  simp [tagScal, tagA, emptyForms, hσ]

/-- The bookkeeping of the nonempty words `R = {r : n_r ≥ 1}` and the empty words. -/
private theorem cII_R_card {p : ℕ} (ns : Fin p → ℕ) (hns : ∑ r, ns r = 3) :
    (Finset.univ.filter fun r => 1 ≤ ns r).card ≤ 3 ∧
      ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ns r = 3 ∧
      (Finset.univ.filter fun r => 1 ≤ ns r).card +
        (Finset.univ.filter fun r => ¬ 1 ≤ ns r).card = p := by
  have h0 : ∑ r ∈ Finset.univ.filter (fun r => ¬ 1 ≤ ns r), ns r = 0 :=
    Finset.sum_eq_zero fun r hr => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Nat.lt_one_iff] at hr
      omega
  have h1 : ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ns r = 3 := by
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => 1 ≤ ns r) ns
    omega
  refine ⟨?_, h1, ?_⟩
  · have : (Finset.univ.filter fun r => 1 ≤ ns r).card ≤
        ∑ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), ns r := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun r hr => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        exact hr
    omega
  · rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

end Words

/-! ## The truncation error `T(G_μμ) − T(P_μ)` on `Θ` -/

section Truncation

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_conjIf_sub (b : Bool) (x y : ℂ) :
    conjIf b x - conjIf b y = conjIf b (x - y) := by
  cases b <;> simp [conjIf, map_sub]

/-- The level `a_μ = 4 K_m (K b + F_v + F_{e_μ})` of the empty words. -/
private def cII_a (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (μ : Fin N) (Km K b : ℝ) : ℝ :=
  4 * Km * (K * b + Fv Sig A z v + Fv Sig A z (eI (Sum.inr μ)))

private theorem cII_whA4 {τ K b Cn Km : ℝ} (hSig : Sig.PosDef)
    {A : Matrix (Fin M) (Fin N) ℝ} (hz : 0 < z.im) {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1) (hKm : 1 ≤ Km) (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (hm : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km) (h : GoodSec8 τ K b Cn Sig A z v μ)
    (i : Fin M) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hn : n = 0) :
    ‖tagA Sig A z v i μ n w σ‖ ≤ cII_a Sig A z v μ Km K b := by
  subst hn
  refine (whA_rough4 hSig hz hb0 hb hKm hv hm h i w σ).trans ?_
  unfold cII_a
  have : b ≤ K * b := le_mul_of_one_le_left hb0 hK
  have h0 : 0 ≤ Km := by linarith
  nlinarith

private theorem cII_a_nonneg {A : Matrix (Fin M) (Fin N) ℝ} {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    {Km K b : ℝ} (hKm : 0 ≤ Km) (hK : 0 ≤ K) (hb : 0 ≤ b) : 0 ≤ cII_a Sig A z v μ Km K b := by
  unfold cII_a Fv
  positivity

/-- On `Θ`, with `|g|, |g'| ≤ 2K`: `|∏_r c_r(A_r g^{t_r}) − ∏_r c_r(A_r g'^{t_r})| ≤
d_μ |g − g'| (2K)^{12} a_μ^{p − q}`. -/
private theorem cII_rep_le {τ K b Cn Km : ℝ} (hSig : Sig.PosDef) {A : Matrix (Fin M) (Fin N) ℝ}
    (hz : 0 < z.im) {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1)
    (hKm : 1 ≤ Km) (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (hm : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km) (h : GoodSec8 τ K b Cn Sig A z v μ)
    (i : Fin M) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) {g g' : ℂ}
    (hg : ‖g‖ ≤ 2 * K) (hg' : ‖g'‖ ≤ 2 * K) :
    ‖cII_T Sig A z v i μ ns ws σs cs g - cII_T Sig A z v i μ ns ws σs cs g'‖ ≤
      (dMuof σs * ‖g - g'‖) * ((2 * K) ^ 12 *
        cII_a Sig A z v μ Km K b ^ (p - (Finset.univ.filter fun r => 1 ≤ ns r).card)) := by
  have h2K : 1 ≤ 2 * K := by linarith
  have hK0 : 0 ≤ K := by linarith
  set a := cII_a Sig A z v μ Km K b with ha
  have ha0 : 0 ≤ a := cII_a_nonneg (by linarith) hK0 hb0
  set m : Fin p → ℝ := fun r => ‖tagA Sig A z v i μ (ns r) (ws r) (σs r)‖ * (2 * K) ^ tagMu (σs r)
    with hm_def
  have hm0 : ∀ r ∈ Finset.univ, 0 ≤ m r := fun r _ => by positivity
  have key := cII_prod_sub_le Finset.univ
    (fun r => conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) (σs r) * g ^ tagMu (σs r)))
    (fun r => conjIf (cs r) (tagA Sig A z v i μ (ns r) (ws r) (σs r) * g' ^ tagMu (σs r)))
    m (fun r => tagMu (σs r) * ‖g - g'‖) hm0
    (fun r _ => by
      simp only [hm_def, cII_norm_conjIf, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg _) (norm_nonneg _))
    (fun r _ => by
      simp only [hm_def, cII_norm_conjIf, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg' _) (norm_nonneg _))
    (fun r _ => by
      simp only [hm_def]
      rw [cII_conjIf_sub, cII_norm_conjIf, ← mul_sub, norm_mul]
      have h1 := cII_pow_sub_le hg hg' (tagMu (σs r))
      have h2 : ((tagMu (σs r) : ℕ) : ℝ) * (2 * K) ^ (tagMu (σs r) - 1) * ‖g - g'‖ ≤
          tagMu (σs r) * ‖g - g'‖ * (2 * K) ^ tagMu (σs r) := by
        have : (2 * K) ^ (tagMu (σs r) - 1) ≤ (2 * K) ^ tagMu (σs r) :=
          pow_le_pow_right₀ h2K (Nat.sub_le _ _)
        have h3 : 0 ≤ ((tagMu (σs r) : ℕ) : ℝ) * ‖g - g'‖ := by positivity
        nlinarith
      calc ‖tagA Sig A z v i μ (ns r) (ws r) (σs r)‖ * ‖g ^ tagMu (σs r) - g' ^ tagMu (σs r)‖
          ≤ ‖tagA Sig A z v i μ (ns r) (ws r) (σs r)‖ *
              (tagMu (σs r) * ‖g - g'‖ * (2 * K) ^ tagMu (σs r)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
        _ = _ := by ring)
  have hsum : ∑ r, (tagMu (σs r) : ℝ) * ‖g - g'‖ = dMuof σs * ‖g - g'‖ := by
    rw [← Finset.sum_mul]; simp [dMuof]
  rw [hsum] at key
  unfold cII_T
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  obtain ⟨hq3, hR3, hcard⟩ := cII_R_card ns hns
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r => 1 ≤ ns r)]
  have hR : ∏ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), m r ≤ (2 * K) ^ 12 := by
    calc ∏ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), m r
        ≤ ∏ r ∈ Finset.univ.filter (fun r => 1 ≤ ns r), (2 * K) ^ (2 * (ns r + 1)) := by
          refine Finset.prod_le_prod₀ (fun r _ => hm0 r (Finset.mem_univ _)) fun r _ => ?_
          simp only [hm_def]
          have h1 := whA_rough3 hK hb0 hb hv h i (ns r) (ws r) (σs r)
          have h2 : (2 * K) ^ tagMu (σs r) ≤ (2 * K) ^ (ns r + 1) :=
            pow_le_pow_right₀ h2K (cII_tagMu_le _)
          calc _ ≤ (2 * K) ^ (ns r + 1) * (2 * K) ^ (ns r + 1) :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = _ := by rw [← pow_add]; ring_nf
      _ = (2 * K) ^ (2 * (3 + (Finset.univ.filter fun r => 1 ≤ ns r).card)) := by
          rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hR3]
          simp
      _ ≤ (2 * K) ^ 12 := pow_le_pow_right₀ h2K (by omega)
  have hE : ∏ r ∈ Finset.univ.filter (fun r => ¬ 1 ≤ ns r), m r ≤
      a ^ (p - (Finset.univ.filter fun r => 1 ≤ ns r).card) := by
    have hc : (Finset.univ.filter fun r => ¬ 1 ≤ ns r).card =
        p - (Finset.univ.filter fun r => 1 ≤ ns r).card := by omega
    rw [← hc, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun r _ => hm0 r (Finset.mem_univ _)) ?_
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Nat.lt_one_iff] at hr
    simp only [hm_def]
    rw [cII_tagMu_zero _ _ hr]
    by_cases hσ : σs r 0 = 0
    · simp only [hσ, ite_true, pow_zero, mul_one]
      exact cII_whA4 hSig hz hK hb0 hb hKm hv hm h i _ _ _ hr
    · simp only [hσ, ite_false, pow_one]
      have h1 := cII_empty_tagA hb0 hb h i _ (ws r) (σs r) hr hσ
      calc _ ≤ 2 * b * (2 * K) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ a := by
            rw [ha]; unfold cII_a
            have h3 : 0 ≤ Fv Sig A z v := norm_nonneg _
            have h4 : 0 ≤ Fv Sig A z (eI (Sum.inr μ)) := norm_nonneg _
            have h5 : 0 ≤ K * b := by positivity
            nlinarith
  exact mul_le_mul hR hE (Finset.prod_nonneg fun r _ => hm0 r (Finset.mem_univ _)) (by positivity)

end Truncation

/-! ## The main term on `Θ`: (818), (819) -/

section MainTerm

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_tagScal_le' {K b : ℝ} {A : Matrix (Fin M) (Fin N) ℝ}
    {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N} (hK : 1 ≤ K) (h : GoodMinor K b Sig A z v μ) (i : Fin M)
    (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (hn : 1 ≤ n) :
    ‖tagScal Sig A z v i μ n w σ‖ ≤ K ^ (n + 1) * cII_u Sig A z v μ i ^ tagF n w σ := by
  cases n with
  | zero => omega
  | succ k => exact cII_tagScal_le hK h i k w σ

private theorem cII_filter_E {p : ℕ} (ns : Fin p → ℕ) :
    (Finset.univ.filter fun r => ¬ 1 ≤ ns r) = Finset.univ.filter fun r => ns r = 0 :=
  Finset.filter_congr fun r _ => by omega

/-- The counts `j₀ = #{r : n_r = 0, σ_r = 0}` and `s = ∑_{n_r = 0} |σ_r|_μ`, with
`j₀ + s + q = p`. -/
private theorem cII_counts {p : ℕ} (ns : Fin p → ℕ) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (hns : ∑ r, ns r = 3) :
    ((Finset.univ.filter fun r => ns r = 0).filter fun r => σs r 0 = 0).card +
        ∑ r ∈ Finset.univ.filter (fun r => ns r = 0), tagMu (σs r) +
        (Finset.univ.filter fun r => 1 ≤ ns r).card = p := by
  obtain ⟨-, -, hcard⟩ := cII_R_card ns hns
  rw [cII_filter_E] at hcard
  have hs : ∑ r ∈ Finset.univ.filter (fun r => ns r = 0), tagMu (σs r) =
      ((Finset.univ.filter fun r => ns r = 0).filter fun r => ¬ σs r 0 = 0).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [cII_tagMu_zero _ _ hr]
    split_ifs <;> simp_all
  rw [hs, Finset.card_filter_add_card_filter_not]
  omega

/-- The sum over `i` of the column averages: `∑_i |E_μ(…)| ≤ 2⁸ τ⁻¹ N K^{12} b^{f ∧ 2}
a_μ^{j₀} C_κ B`. -/
private theorem cII_main_mu {K b Cn Km Kt0 Bd : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hSig : Sig.PosDef)
    {A : Matrix (Fin M) (Fin N) ℝ} (hz : 0 < z.im) {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1) (hKm : 1 ≤ Km) (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (hm : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (h : GoodSec8 τ K b Cn Sig A z v μ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ)
    (ν : Measure (Fin M → ℝ)) (hKt0 : 0 ≤ Kt0) (hBd : 0 ≤ Bd)
    (hKt : ((Kt + 1) * ((Kt + 1) * 2 ^ Kt * (2 * K) ^ (2 * Kt + 1)) : ℝ) ^ dMuof σs ≤ Kt0)
    (hint : ∀ (i : Fin M) (k : ℕ) (ct : Fin k → Bool), Integrable (fun y : Fin M → ℝ =>
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)) ν)
    (hL : ∀ (i : Fin M) (k : ℕ) (ct : Fin k → Bool), k ≤ Kt * dMuof σs → ‖∫ y,
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) ∂ν‖ ≤ Bd) :
    ∑ i, ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt) ∂ν‖ ≤
      2 ^ 8 * τ⁻¹ * N * K ^ 12 * b ^ (min (∑ r, tagF (ns r) (ws r) (σs r)) 2) *
        cII_a Sig A z v μ Km K b ^ ((Finset.univ.filter fun r => ns r = 0).filter
          fun r => σs r 0 = 0).card * (Kt0 * Bd) := by
  have hK0 : 0 ≤ K := by linarith
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  obtain ⟨hq3, hR3, -⟩ := cII_R_card ns hns
  set a := cII_a Sig A z v μ Km K b with ha
  have ha0 : 0 ≤ a := cII_a_nonneg (by linarith) hK0 hb0
  set R := Finset.univ.filter fun r => 1 ≤ ns r with hRdef
  set E := Finset.univ.filter fun r => ns r = 0 with hEdef
  set f := ∑ r, tagF (ns r) (ws r) (σs r) with hf
  set j0 := (E.filter fun r => σs r 0 = 0).card with hj0
  have hfR : ∑ r ∈ R, tagF (ns r) (ws r) (σs r) = f := by
    rw [hf, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => 1 ≤ ns r)]
    have : ∑ r ∈ Finset.univ.filter (fun r => ¬ 1 ≤ ns r), tagF (ns r) (ws r) (σs r) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Nat.lt_one_iff] at hr
        exact cII_tagF_zero _ _ _ hr
    rw [this, add_zero]
  have hf6 : f ≤ 6 := by
    have : f ≤ ∑ r, 2 * ns r := Finset.sum_le_sum fun r _ => cII_tagF_le _ _ _
    rw [← Finset.mul_sum, hns] at this
    omega
  -- the scalar parts
  have hscal : ∀ i, ∏ r, ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖ ≤
      K ^ 6 * cII_u Sig A z v μ i ^ f * a ^ j0 := by
    intro i
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r => 1 ≤ ns r), cII_filter_E]
    have hu0 : 0 ≤ cII_u Sig A z v μ i := by unfold cII_u; positivity
    have h1 : ∏ r ∈ R, ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖ ≤
        K ^ 6 * cII_u Sig A z v μ i ^ f := by
      calc ∏ r ∈ R, ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖
          ≤ ∏ r ∈ R, K ^ (ns r + 1) * cII_u Sig A z v μ i ^ tagF (ns r) (ws r) (σs r) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r hr => by
              simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hr
              exact cII_tagScal_le' hK h.toGoodMinor i _ _ _ hr
        _ = K ^ (∑ r ∈ R, (ns r + 1)) * cII_u Sig A z v μ i ^ f := by
            rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
              hfR]
        _ ≤ K ^ 6 * cII_u Sig A z v μ i ^ f := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK ?_) (by positivity)
            rw [Finset.sum_add_distrib, hR3]; simp; omega
    have h2 : ∏ r ∈ E, ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖ ≤ a ^ j0 := by
      rw [← Finset.prod_filter_mul_prod_filter_not E (fun r => σs r 0 = 0)]
      have e1 : ∏ r ∈ E.filter (fun r => σs r 0 = 0), ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖
          ≤ a ^ j0 := by
        rw [hj0, ← Finset.prod_const]
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r hr => ?_
        simp only [hEdef, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rw [cII_empty_scal_zero i _ _ _ hr.1 hr.2]
        exact cII_whA4 hSig hz hK hb0 hb hKm hv hm h i _ _ _ hr.1
      have e2 : ∏ r ∈ E.filter (fun r => ¬ σs r 0 = 0),
          ‖tagScal Sig A z v i μ (ns r) (ws r) (σs r)‖ = 1 := by
        refine Finset.prod_eq_one fun r hr => ?_
        simp only [hEdef, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        exact cII_empty_scal_one i _ _ _ hr.1 hr.2
      rw [e2, mul_one]; exact e1
    exact (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity))
  calc ∑ i, ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs
        (cII_P Sig (updCol A μ y) z μ Kt) ∂ν‖
      ≤ ∑ i, (K ^ 6 * cII_u Sig A z v μ i ^ f * a ^ j0) * (Kt0 * Bd) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (cII_g_le A v i μ ns ws σs cs Kt ν hK (h.y_le.trans (by linarith))
          (h.zy_le) (hint i) (hL i)).trans ?_
        have hu0 : 0 ≤ cII_u Sig A z v μ i := by unfold cII_u; positivity
        refine mul_le_mul (hscal i) (mul_le_mul_of_nonneg_right hKt hBd) (by positivity)
          (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hu0 _)) (pow_nonneg ha0 _))
    _ = K ^ 6 * a ^ j0 * (Kt0 * Bd) * ∑ i, cII_u Sig A z v μ i ^ f := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ K ^ 6 * a ^ j0 * (Kt0 * Bd) * (4 * τ⁻¹ * N * (2 * K) ^ f * b ^ (min f 2)) :=
        mul_le_mul_of_nonneg_left (cII_sum_u_le hτ hτ1 hK hb0 hM h.toGoodMinor f) (by positivity)
    _ ≤ K ^ 6 * a ^ j0 * (Kt0 * Bd) * (4 * τ⁻¹ * N * (2 ^ 6 * K ^ 6) * b ^ (min f 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        calc (2 * K) ^ f ≤ (2 * K) ^ 6 := pow_le_pow_right₀ (by linarith) hf6
          _ = 2 ^ 6 * K ^ 6 := by ring
    _ = 2 ^ 8 * τ⁻¹ * N * K ^ 12 * b ^ (min f 2) * a ^ j0 * (Kt0 * Bd) := by ring

end MainTerm

/-! ## Power counting: the weights (sec8 4), the absorption (sec8 5), Young -/

section Counting

private theorem cII_rpow_half (N : ℕ) : (N : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]; ring_nf

private theorem cII_rpow_three_half (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * N = (N : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add_one hNp.ne']; norm_num

private theorem cII_half_sq (hN : 1 ≤ N) : ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (N : ℝ)⁻¹ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cII_rpow_half N, inv_pow, Real.sq_sqrt hNp.le]

/-- The weights `w'_μ` of (sec8 4). -/
private def cII_w (N : ℕ) (dv : ℕ) (x : ℝ) : ℝ :=
  if dv = 0 then (N : ℝ)⁻¹ else if dv = 1 then (N : ℝ) ^ (-(1 : ℝ) / 2) * |x| else x ^ 2

private theorem cII_w_nonneg (N dv : ℕ) (x : ℝ) : 0 ≤ cII_w N dv x := by
  unfold cII_w
  split_ifs
  · positivity
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _)
  · positivity

/-- `∑_μ w'_μ ≤ 1` for `|v| = 1`. -/
private theorem cII_w_sum {Sig : Matrix (Fin M) (Fin M) ℝ} {v : Fin M ⊕ Fin N → ℝ}
    (hv : testNorm v = 1) (hN : 1 ≤ N) (dv : ℕ) :
    ∑ μ, cII_w N dv (vbar Sig v (Sum.inr μ)) ≤ 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hvv : ∀ μ, vbar Sig v (Sum.inr μ) = v (Sum.inr μ) := fun μ => by simp [vbar]
  have hs : ∑ μ, v (Sum.inr μ) ^ 2 ≤ 1 := by
    have h : ∑ s, v s ^ 2 = 1 := by
      unfold testNorm at hv; rwa [Real.sqrt_eq_one] at hv
    rw [Fintype.sum_sum_type] at h
    have h0 : 0 ≤ ∑ i, v (Sum.inl i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  unfold cII_w
  simp only [hvv]
  split_ifs with h0 h1
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_cancel₀ hNp.ne']
  · rw [← Finset.mul_sum]
    have hc : (∑ μ, |v (Sum.inr μ)|) ^ 2 ≤ N * ∑ μ, |v (Sum.inr μ)| ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
        (f := fun μ => |v (Sum.inr μ)|)
      simpa using this
    simp only [sq_abs] at hc
    have h2 : ∑ μ, |v (Sum.inr μ)| ≤ Real.sqrt N := by
      rw [← Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      exact Real.sqrt_le_sqrt (hc.trans (by nlinarith))
    rw [cII_rpow_half N]
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    calc (Real.sqrt N)⁻¹ * ∑ μ, |v (Sum.inr μ)| ≤ (Real.sqrt N)⁻¹ * Real.sqrt N :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := inv_mul_cancel₀ hsq.ne'
  · exact hs

/-- (sec8 4): `N^{−3/2} |v̄(μ)|^{d_v} N β b^m ≤ w'_μ b^e`, with
`β = N^{−[d_v = 0]/2} b^{d_X − [d_X ≥ 3][d_v = 0]}` and
`e = d_X + [d_v ≥ 2] + m − [d_X ≥ 3][d_v = 0]`. -/
private theorem cII_weight_le (hN : 1 ≤ N) {b x : ℝ} (hb0 : 0 ≤ b)
    (hbN : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b) (hx : |x| ≤ 1) (dv dX m : ℕ) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * (|x| ^ dv * (N * ((if dv = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
        b ^ (dX - if 3 ≤ dX then 1 else 0) else b ^ dX) * b ^ m))) ≤
      cII_w N dv x * b ^ (dX + (if 2 ≤ dv then 1 else 0) + m -
        (if 3 ≤ dX ∧ dv = 0 then 1 else 0)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hNp.le _
  have e3 := cII_rpow_three_half hN
  have e2 := cII_half_sq hN
  unfold cII_w
  rcases Nat.lt_or_ge dv 2 with hdv | hdv
  · interval_cases dv
    · simp only [pow_zero, one_mul, ite_true, show ¬ (2 ≤ 0) from by omega, ite_false, add_zero,
        and_true]
      have e : (N : ℝ) ^ (-(3 : ℝ) / 2) * (N * ((N : ℝ) ^ (-(1 : ℝ) / 2) *
          b ^ (dX - if 3 ≤ dX then 1 else 0) * b ^ m)) =
          ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 * b ^ ((dX - if 3 ≤ dX then 1 else 0) + m) := by
        rw [pow_add, ← mul_assoc ((N : ℝ) ^ (-(3 : ℝ) / 2)), e3]; ring
      rw [e, e2]
      apply le_of_eq
      congr 2
      split_ifs with h3 <;> omega
    · simp only [pow_one, one_ne_zero, ite_false, ite_true, show ¬ (2 ≤ 1) from by omega,
        add_zero, and_false, Nat.sub_zero]
      have e : (N : ℝ) ^ (-(3 : ℝ) / 2) * (|x| * (N * (b ^ dX * b ^ m))) =
          (N : ℝ) ^ (-(1 : ℝ) / 2) * |x| * b ^ (dX + m) := by
        rw [pow_add, ← e3]; ring
      rw [e]
  · have h0 : dv ≠ 0 := by omega
    have h1 : dv ≠ 1 := by omega
    simp only [h0, h1, ite_false, hdv, ite_true, and_false, Nat.sub_zero]
    have hxp : |x| ^ dv ≤ x ^ 2 := by
      rw [← sq_abs x]
      calc |x| ^ dv = |x| ^ 2 * |x| ^ (dv - 2) := by rw [← pow_add]; congr 1; omega
        _ ≤ |x| ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hx)
            (sq_nonneg _)
        _ = |x| ^ 2 := mul_one _
    calc (N : ℝ) ^ (-(3 : ℝ) / 2) * (|x| ^ dv * (N * (b ^ dX * b ^ m)))
        = (N : ℝ) ^ (-(1 : ℝ) / 2) * |x| ^ dv * b ^ (dX + m) := by
          rw [pow_add, ← e3]; ring
      _ ≤ b * x ^ 2 * b ^ (dX + m) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hbN hxp (by positivity) hb0)
            (by positivity)
      _ = x ^ 2 * b ^ (dX + 1 + m) := by ring

/-- (sec8 5): `L = 12 + d_X + (3K_τ + 1) d_μ ≤ (15 K_τ + 24) e` when `e ≥ 1`, `d_X ≤ e + 1`,
`d_μ ≤ d_X + 3`. -/
private theorem cII_L_le (Kt dX dMu e : ℕ) (he : 1 ≤ e) (hX : dX ≤ e + 1) (hMu : dMu ≤ dX + 3) :
    12 + dX + Kt * dMu + (2 * Kt + 1) * dMu ≤ (15 * Kt + 24) * e := by
  have h1 : dMu ≤ e + 4 := by omega
  have h2 : Kt * dMu ≤ Kt * (e + 4) := Nat.mul_le_mul_left _ h1
  have h3 : (2 * Kt + 1) * dMu ≤ (2 * Kt + 1) * (e + 4) := Nat.mul_le_mul_left _ h1
  have h4 : 12 * Kt + 17 ≤ (12 * Kt + 22) * e := by nlinarith
  nlinarith

/-- `K^L b^e ≤ B^{q+s}` for `B = K^β b ≤ 1`, `L ≤ β e`, `e ≥ q + s`. -/
private theorem cII_absorb {K b : ℝ} (hK : 1 ≤ K) (hb0 : 0 ≤ b) {L β e qs : ℕ} (hL : L ≤ β * e)
    (hqs : qs ≤ e) (hB : K ^ β * b ≤ 1) : K ^ L * b ^ e ≤ (K ^ β * b) ^ qs := by
  have hB0 : 0 ≤ K ^ β * b := by have : 0 ≤ K := by linarith
                                 positivity
  calc K ^ L * b ^ e ≤ K ^ (β * e) * b ^ e :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hL) (pow_nonneg hb0 _)
    _ = (K ^ β * b) ^ e := by rw [mul_pow, pow_mul]
    _ ≤ (K ^ β * b) ^ qs := pow_le_pow_of_le_one hB0 hB hqs

/-- Young's inequality in the form `B^{q} a^{p − q} ≤ B^p + a^p`. -/
private theorem cII_young {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) {p q : ℕ} (hqp : q ≤ p) (hp : 0 < p) :
    B ^ q * a ^ (p - q) ≤ B ^ p + a ^ p := by
  have h := young_pow ha hB hqp hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : ((p - q : ℕ) : ℝ) / p ≤ 1 := by
    rw [div_le_one hp']; exact_mod_cast Nat.sub_le p q
  have h2 : (q : ℝ) / p ≤ 1 := by rw [div_le_one hp']; exact_mod_cast hqp
  have h3 : ((p - q : ℕ) : ℝ) / p * a ^ p ≤ a ^ p :=
    mul_le_of_le_one_left (pow_nonneg ha _) h1
  have h4 : (q : ℝ) / p * B ^ p ≤ B ^ p := mul_le_of_le_one_left (pow_nonneg hB _) h2
  rw [mul_comm]
  linarith

end Counting

/-! ## The bound on `Θ` for one `μ` -/

section OneMu

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

/-- The constant `c_κ = (K_τ + 1)² 2^{K_τ} 2^{2K_τ+1}` of the coefficients `𝒵`. -/
private def cII_ck (Kt : ℕ) : ℝ := (Kt + 1) ^ 2 * 2 ^ Kt * 2 ^ (2 * Kt + 1)

private theorem cII_ck_one (Kt : ℕ) : 1 ≤ cII_ck Kt := by
  unfold cII_ck
  have h1 : (1 : ℝ) ≤ (Kt + 1) ^ 2 := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) Kt; linarith)
  have h2 : (1 : ℝ) ≤ 2 ^ Kt := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ 2 ^ (2 * Kt + 1) := one_le_pow₀ (by norm_num)
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) h3 zero_le_one
        (by positivity)

private theorem cII_dMu_le {p : ℕ} (ns : Fin p → ℕ) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (hns : ∑ r, ns r = 3) : dMuof σs ≤ p + 3 := by
  unfold dMuof
  calc ∑ r, tagMu (σs r) ≤ ∑ r, (ns r + 1) := Finset.sum_le_sum fun r _ => cII_tagMu_le _
    _ = p + 3 := by rw [Finset.sum_add_distrib, hns]; simp [add_comm]

/-- The main term at one `μ`, with the weight of (sec8 4), the absorption (sec8 5) and Young:
`N^{−3/2} |v̄(μ)|^{d_v} ∑_i |E_μ(…)| ≤ c₈ w'_μ (B^p + a_μ^p)`, `B = K^{15K_τ+24} b`. -/
private theorem cII_mu_main {K b Cn Km Kmax : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hSig : Sig.PosDef)
    {A : Matrix (Fin M) (Fin N) ℝ} (hz : 0 < z.im) {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1) (hbN : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b)
    (hKm : 1 ≤ Km) (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (hm : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (h : GoodSec8 τ K b Cn Sig A z v μ) {p : ℕ} (hp : 0 < p) (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (Kt : ℕ)
    (hB : K ^ (15 * Kt + 24) * b ≤ 1) (hKmax : 0 ≤ Kmax) (ν : Measure (Fin M → ℝ))
    (hint : ∀ (i : Fin M) (k : ℕ) (ct : Fin k → Bool), Integrable (fun y : Fin M → ℝ =>
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)) ν)
    (hL : ∀ (i : Fin M) (k : ℕ) (ct : Fin k → Bool), k ≤ Kt * dMuof σs → ‖∫ y,
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) ∂ν‖ ≤
        Kmax * K ^ (dXof ns ws σs + Kt * dMuof σs) *
          (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
              b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0)
            else b ^ dXof ns ws σs)) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dVof σs * ∑ i,
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt) ∂ν‖) ≤
      (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) * cII_w N (dVof σs) (vbar Sig v (Sum.inr μ)) *
        ((K ^ (15 * Kt + 24) * b) ^ p + cII_a Sig A z v μ Km K b ^ p) := by
  have hK0 : 0 ≤ K := by linarith
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hcomb, hMuX⟩ := main_comb_est ns ws σs hns hnz
  have hcount := cII_counts ns σs hns
  obtain ⟨-, hR3, -⟩ := cII_R_card ns hns
  have hmain := cII_main_mu (Kt0 := cII_ck Kt ^ (p + 3) * K ^ ((2 * Kt + 1) * dMuof σs))
    (Bd := Kmax * K ^ (dXof ns ws σs + Kt * dMuof σs) *
      (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
          b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0) else b ^ dXof ns ws σs))
    hτ hτ1 hSig hz hK hb0 hb hKm hv hm hM h ns ws σs cs hns Kt ν
  set dX := dXof ns ws σs with hdX
  set dv := dVof σs with hdv
  set dMu := dMuof σs with hdMu
  set f := ∑ r, tagF (ns r) (ws r) (σs r) with hf
  set a := cII_a Sig A z v μ Km K b with ha
  have ha0 : 0 ≤ a := cII_a_nonneg (by linarith) hK0 hb0
  set B := K ^ (15 * Kt + 24) * b with hBdef
  have hB0 : 0 ≤ B := by positivity
  set q := (Finset.univ.filter fun r => 1 ≤ ns r).card with hq
  set sE := ∑ r ∈ Finset.univ.filter (fun r => ns r = 0), tagMu (σs r) with hsE
  set j0 := ((Finset.univ.filter fun r => ns r = 0).filter fun r => σs r 0 = 0).card with hj0
  have hq1 : 1 ≤ q := by
    by_contra h0
    have : q = 0 := by omega
    rw [hq, Finset.card_eq_zero] at this
    rw [this, Finset.sum_empty] at hR3
    omega
  set e := dX + (if 2 ≤ dv then 1 else 0) + min f 2 - (if 3 ≤ dX ∧ dv = 0 then 1 else 0) with he
  have hqse : q + sE ≤ e := by omega
  have he1 : 1 ≤ e := by omega
  have hXe : dX ≤ e + 1 := by
    have : (if 3 ≤ dX ∧ dv = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega
  have hj0' : j0 = p - (q + sE) := by omega
  have hqsp : q + sE ≤ p := by omega
  set Bd := Kmax * K ^ (dX + Kt * dMu) *
    (if dv = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) * b ^ (dX - if 3 ≤ dX then 1 else 0) else b ^ dX)
    with hBd
  have hβ0 : 0 ≤ (if dv = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) * b ^ (dX - if 3 ≤ dX then 1 else 0)
      else b ^ dX) := by
    split_ifs <;> first
      | exact pow_nonneg hb0 _
      | exact mul_nonneg (Real.rpow_nonneg hNp.le _) (pow_nonneg hb0 _)
  have hBd0 : 0 ≤ Bd := by positivity
  set Kt0 := cII_ck Kt ^ (p + 3) * K ^ ((2 * Kt + 1) * dMu) with hKt0
  have hck := cII_ck_one Kt
  have hKt0' : (((Kt + 1) * ((Kt + 1) * 2 ^ Kt * (2 * K) ^ (2 * Kt + 1)) : ℝ)) ^ dMu ≤ Kt0 := by
    have e1 : (((Kt + 1) * ((Kt + 1) * 2 ^ Kt * (2 * K) ^ (2 * Kt + 1)) : ℝ)) ^ dMu =
        cII_ck Kt ^ dMu * K ^ ((2 * Kt + 1) * dMu) := by
      have eb : (((Kt + 1) * ((Kt + 1) * 2 ^ Kt * (2 * K) ^ (2 * Kt + 1)) : ℝ)) =
          cII_ck Kt * K ^ (2 * Kt + 1) := by
        unfold cII_ck; rw [mul_pow]; ring
      rw [eb, mul_pow, pow_mul]
    rw [e1, hKt0]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hck (cII_dMu_le ns σs hns))
      (by positivity)
  have hmain := hmain (by positivity) hBd0 hKt0' hint hL
  have hw0 := cII_w_nonneg N dv (vbar Sig v (Sum.inr μ))
  have hwt := cII_weight_le hN hb0 hbN hv dv dX (min f 2)
  have hLle := cII_L_le Kt dX dMu e he1 hXe hMuX
  have habs := cII_absorb hK hb0 hLle hqse hB
  have hyoung := cII_young ha0 hB0 hqsp hp
  rw [← hj0'] at hyoung
  have hvd0 : 0 ≤ |vbar Sig v (Sum.inr μ)| ^ dv := by positivity
  have hpre0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hNp.le _
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dv * ∑ i,
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt) ∂ν‖)
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dv *
          (2 ^ 8 * τ⁻¹ * N * K ^ 12 * b ^ (min f 2) * a ^ j0 * (Kt0 * Bd))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain hvd0) hpre0
    _ = (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) * (K ^ (12 + dX + Kt * dMu +
          (2 * Kt + 1) * dMu) * a ^ j0) * ((N : ℝ) ^ (-(3 : ℝ) / 2) *
          (|vbar Sig v (Sum.inr μ)| ^ dv * (N * ((if dv = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
            b ^ (dX - if 3 ≤ dX then 1 else 0) else b ^ dX) * b ^ (min f 2))))) := by
        rw [hBd, hKt0]
        simp only [pow_add]
        ring
    _ ≤ (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) * (K ^ (12 + dX + Kt * dMu +
          (2 * Kt + 1) * dMu) * a ^ j0) * (cII_w N dv (vbar Sig v (Sum.inr μ)) * b ^ e) :=
        mul_le_mul_of_nonneg_left hwt (by positivity)
    _ = (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) * cII_w N dv (vbar Sig v (Sum.inr μ)) *
          ((K ^ (12 + dX + Kt * dMu + (2 * Kt + 1) * dMu) * b ^ e) * a ^ j0) := by ring
    _ ≤ (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) * cII_w N dv (vbar Sig v (Sum.inr μ)) *
          (B ^ (q + sE) * a ^ j0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right habs (pow_nonneg ha0 _))
          (by positivity)
    _ ≤ (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) * cII_w N dv (vbar Sig v (Sum.inr μ)) *
          (B ^ p + a ^ p) := mul_le_mul_of_nonneg_left hyoung (by positivity)

end OneMu

private theorem cII_zY_le_aux {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (μ : Fin N) :
    -z - Ymu Sig A z μ ≠ 0 := by
  intro h
  have := (calY_rough hSig A hz μ).1
  rw [h, Complex.zero_im] at this
  linarith

section OneMuRep

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

/-- The truncation error at one `μ`:
`N^{−3/2} |v̄(μ)|^{d_v} ∑_i |T(G_μμ) − T(P_μ)| ≤ N⁻¹ a_μ^p`, when
`ε = K (2K² N^{−τ/2})^{K_τ+1}` satisfies `ε ≤ K` and `τ⁻¹ N² (p + 3) ε (2K)^{12} ≤ 1`. -/
private theorem cII_mu_rep {K b Cn Km : ℝ} (hτ : 0 < τ) (hSig : Sig.PosDef)
    {A : Matrix (Fin M) (Fin N) ℝ} (hz : 0 < z.im) {v : Fin M ⊕ Fin N → ℝ} {μ : Fin N}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1) (hbN : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b)
    (hKm : 1 ≤ Km) (hv : |vbar Sig v (Sum.inr μ)| ≤ 1)
    (hm : ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ Km) (hM : (M : ℝ) ≤ τ⁻¹ * N)
    (h : GoodSec8 τ K b Cn Sig A z v μ) {p : ℕ} (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (Kt : ℕ)
    (hε : K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) ≤ K)
    (hrep : τ⁻¹ * (N : ℝ) ^ 2 * (p + 3) * (K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1)) *
      (2 * K) ^ 12 ≤ 1) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dVof σs * ∑ i,
        ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖) ≤
      (N : ℝ)⁻¹ * cII_a Sig A z v μ Km K b ^ p := by
  have hK0 : 0 ≤ K := by linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  set ε := K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  set a := cII_a Sig A z v μ Km K b with ha
  have ha0 : 0 ≤ a := cII_a_nonneg (by linarith) hK0 hb0
  set t := (N : ℝ) ^ (-(1 : ℝ) / 2) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hNp.le _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have hta : t ≤ a := by
    refine hbN.trans ?_
    rw [ha]; unfold cII_a
    have h3 : 0 ≤ Fv Sig A z v := norm_nonneg _
    have h4 : 0 ≤ Fv Sig A z (eI (Sum.inr μ)) := norm_nonneg _
    have h5 : b ≤ K * b := le_mul_of_one_le_left hb0 hK
    nlinarith
  -- `G_μμ − P_μ`
  have hY := (cII_zY_le_aux hSig A hz μ)
  have hexp := gmumu_exp hSig A hz μ Kt hY
  have hGP : ‖G Sig A z (Sum.inr μ) (Sum.inr μ) - cII_P Sig A z μ Kt‖ ≤ ε := by
    have e : G Sig A z (Sum.inr μ) (Sum.inr μ) - cII_P Sig A z μ Kt =
        G Sig A z (Sum.inr μ) (Sum.inr μ) *
          ((Qmu Sig A z μ - Ymu Sig A z μ) * (-z - Ymu Sig A z μ)⁻¹) ^ (Kt + 1) := by
      unfold cII_P
      conv_lhs => rw [hexp]
      ring
    rw [e, norm_mul, norm_pow, norm_mul]
    refine mul_le_mul h.gmumu_le (pow_le_pow_left₀ (by positivity)
      (mul_le_mul h.z_le h.zy_le (norm_nonneg _) (by positivity)) _) (by positivity) hK0
  have hG : ‖G Sig A z (Sum.inr μ) (Sum.inr μ)‖ ≤ 2 * K := by linarith [h.gmumu_le]
  have hP : ‖cII_P Sig A z μ Kt‖ ≤ 2 * K := by
    have := norm_sub_norm_le (G Sig A z (Sum.inr μ) (Sum.inr μ)) (cII_P Sig A z μ Kt)
    have h2 := norm_sub_rev (G Sig A z (Sum.inr μ) (Sum.inr μ)) (cII_P Sig A z μ Kt)
    have h3 := norm_le_insert' (cII_P Sig A z μ Kt) (G Sig A z (Sum.inr μ) (Sum.inr μ))
    linarith [h.gmumu_le]
  obtain ⟨hq3, -, -⟩ := cII_R_card ns hns
  set q := (Finset.univ.filter fun r => 1 ≤ ns r).card with hq
  have hqp : q ≤ p := by
    rw [hq]; exact (Finset.card_filter_le _ _).trans (by simp)
  have hapq : t ^ 3 * a ^ (p - q) ≤ a ^ p := by
    calc t ^ 3 * a ^ (p - q) ≤ t ^ q * a ^ (p - q) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0 ht1 hq3) (pow_nonneg ha0 _)
      _ ≤ a ^ q * a ^ (p - q) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 hta q)
          (pow_nonneg ha0 _)
      _ = a ^ p := by rw [← pow_add]; congr 1; omega
  have ht3 : t ^ 3 = (N : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num
  have hdMu := cII_dMu_le ns σs hns
  have hterm : ∀ i, ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
      cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ ≤
      (p + 3) * ε * ((2 * K) ^ 12 * a ^ (p - q)) := by
    intro i
    refine (cII_rep_le hSig hz hK hb0 hb hKm hv hm h i ns ws σs cs hns hG hP).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (dMuof σs : ℝ) ≤ p + 3 := by exact_mod_cast hdMu
    exact mul_le_mul this hGP (norm_nonneg _) (by positivity)
  have hvd : |vbar Sig v (Sum.inr μ)| ^ dVof σs ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
  have hsum : ∑ i, ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
      cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ ≤
      M * ((p + 3) * ε * ((2 * K) ^ 12 * a ^ (p - q))) := by
    calc _ ≤ ∑ _i : Fin M, (p + 3) * ε * ((2 * K) ^ 12 * a ^ (p - q)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp
  have hS0 : 0 ≤ ∑ i, ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
      cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpre0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hNp.le _
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dVof σs * ∑ i,
        ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖)
      ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * (1 * (M * ((p + 3) * ε * ((2 * K) ^ 12 * a ^ (p - q))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hvd hsum hS0 zero_le_one) hpre0
    _ = M * (p + 3) * ε * (2 * K) ^ 12 * (t ^ 3 * a ^ (p - q)) := by rw [ht3]; ring
    _ ≤ (τ⁻¹ * N) * (p + 3) * ε * (2 * K) ^ 12 * a ^ p := by
        have h1 : (0 : ℝ) ≤ (p + 3) * ε * (2 * K) ^ 12 := by positivity
        calc (M : ℝ) * (p + 3) * ε * (2 * K) ^ 12 * (t ^ 3 * a ^ (p - q))
            ≤ (M : ℝ) * (p + 3) * ε * (2 * K) ^ 12 * a ^ p :=
              mul_le_mul_of_nonneg_left hapq (by positivity)
          _ ≤ (τ⁻¹ * N) * (p + 3) * ε * (2 * K) ^ 12 * a ^ p := by
              have := mul_le_mul_of_nonneg_right hM (mul_nonneg h1 (pow_nonneg ha0 p))
              nlinarith
    _ = (N : ℝ)⁻¹ * ((τ⁻¹ * (N : ℝ) ^ 2 * (p + 3) * ε * (2 * K) ^ 12) * a ^ p) := by
        field_simp
    _ ≤ (N : ℝ)⁻¹ * (1 * a ^ p) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrep (pow_nonneg ha0 _))
          (by positivity)
    _ = (N : ℝ)⁻¹ * a ^ p := by ring

end OneMuRep

/-! ## Rough bounds on the random variables and their integrability -/

section RoughRV

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_Fv_le {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) {w : Fin M ⊕ Fin N → ℝ} (hw : testNorm w = 1) :
    Fv Sig A z w ≤ roughConst τ c * (N * (1 + cII_sq A)) := by
  have hF := cII_facts hset hz
  have hM1 := hF.M1
  have h := norm_wordA_rough hset hz A w hw ⟨0, by omega⟩ ⟨0, by have := hF.N1; omega⟩ 0
    (fun x => Fin.elim0 x)
  simp only [wordA, zero_add, pow_one] at h
  refine h.trans ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (cII_Lam_le hF A) (zero_le_one.trans hF.rough1)

private theorem cII_U_updCol (hF : cII_Facts (N := N) τ c Sig z) (A : Matrix (Fin M) (Fin N) ℝ)
    (μ : Fin N) (y : Fin M → ℝ) : cII_U τ c (updCol A μ y) ≤ cII_U τ c A * cII_W y ^ 2 := by
  unfold cII_U
  have h1 := cII_sq_updCol A μ y
  have h0 := cII_sq_nonneg A
  have hW : 1 + cII_sq (updCol A μ y) ≤ (1 + cII_sq A) * cII_W y := by
    unfold cII_W
    have : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have hc : 0 ≤ cII_cU τ c := by
    unfold cII_cU; have := hF.rough1; have := hF.Km1; have := hF.pos; positivity
  have h2 : (1 + cII_sq (updCol A μ y)) ^ 2 ≤ ((1 + cII_sq A) * cII_W y) ^ 2 :=
    pow_le_pow_left₀ (by have := cII_sq_nonneg (updCol A μ y); linarith) hW 2
  calc cII_cU τ c * (N : ℝ) ^ 2 * (1 + cII_sq (updCol A μ y)) ^ 2
      ≤ cII_cU τ c * (N : ℝ) ^ 2 * ((1 + cII_sq A) * cII_W y) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- The rough constant `c_T = ((K_τ+1)² 2^{K_τ})^{p+3}`. -/
private def cII_cT (Kt p : ℕ) : ℝ := (((Kt : ℝ) + 1) ^ 2 * 2 ^ Kt) ^ (p + 3)

private theorem cII_cT_one (Kt p : ℕ) : 1 ≤ cII_cT Kt p := by
  unfold cII_cT
  refine one_le_pow₀ ?_
  have h1 : (1 : ℝ) ≤ ((Kt : ℝ) + 1) ^ 2 :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) Kt; linarith)
  have h2 : (1 : ℝ) ≤ 2 ^ Kt := one_le_pow₀ (by norm_num)
  nlinarith

/-- `|T(G_μμ)|, |T(P_μ)| ≤ c_T U^{(3K_τ+4)(p+3)}`. -/
private theorem cII_TT_TP_le {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M)
    (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ) :
    ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ))‖ ≤
        cII_cT Kt p * cII_U τ c A ^ ((3 * Kt + 4) * (p + 3)) ∧
      ‖cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ ≤
        cII_cT Kt p * cII_U τ c A ^ ((3 * Kt + 4) * (p + 3)) := by
  have hF := cII_facts hset hz
  have hU := cII_U_one hF A
  have hcT := cII_cT_one Kt p
  constructor
  · have h := cII_T_le hset hz A hv i μ ns ws σs cs hns (cg := 1) (a := 1) le_rfl
      (by rw [one_mul, pow_one]; exact cII_Gmumu_le hF A μ)
    refine h.trans ?_
    rw [one_mul, ← pow_mul]
    calc cII_U τ c A ^ ((1 + 3) * (p + 3)) ≤ cII_U τ c A ^ ((3 * Kt + 4) * (p + 3)) :=
          pow_le_pow_right₀ hU (Nat.mul_le_mul_right _ (by omega))
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hcT
  · have hcg : (1 : ℝ) ≤ ((Kt : ℝ) + 1) ^ 2 * 2 ^ Kt := by
      have h1 : (1 : ℝ) ≤ ((Kt : ℝ) + 1) ^ 2 :=
        one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) Kt; linarith)
      have h2 : (1 : ℝ) ≤ 2 ^ Kt := one_le_pow₀ (by norm_num)
      nlinarith
    have h := cII_T_le hset hz A hv i μ ns ws σs cs hns hcg (cII_P_le hF A μ Kt)
    refine h.trans (le_of_eq ?_)
    unfold cII_cT
    rw [mul_pow, ← pow_mul]

/-- Integrability of a continuous function of `X` bounded by `c U(X)^n`. -/
private theorem cII_integrable_U {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    (hF : cII_Facts (N := N) τ c Sig z) {E : Type*} [NormedAddCommGroup E]
    {f : Matrix (Fin M) (Fin N) ℝ → E} (hf : AEStronglyMeasurable (fun ω => f (X ω)) ℙ)
    {cf : ℝ} {n : ℕ} (hb : ∀ A, ‖f A‖ ≤ cf * cII_U τ c A ^ n) :
    Integrable fun ω => f (X ω) := by
  have hW := (cII_moment_W hF.pos hX hF.N1 hF.Mle (2 * n)).1
  refine (hW.const_mul (cf * (cII_cU τ c * (N : ℝ) ^ 2) ^ n)).mono' hf (ae_of_all _ fun ω => ?_)
  refine (hb (X ω)).trans (le_of_eq ?_)
  unfold cII_U
  rw [mul_pow, pow_mul]; ring

end RoughRV

/-! ## The column average as a random variable -/

section ColAvg

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_continuous_TP (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (Kt : ℕ) :
    Continuous fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin N) ℝ =>
      cII_T Sig (updCol q.2 μ q.1) z v i μ ns ws σs cs (cII_P Sig (updCol q.2 μ q.1) z μ Kt) :=
  (cII_continuous_T hSig hz v i μ ns ws σs cs (cII_continuous_P hSig hz μ Kt)).comp
    (cII_continuous_updCol μ)

private theorem cII_gg_meas (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (Kt : ℕ) (ν : Measure (Fin M → ℝ))
    [SFinite ν] :
    StronglyMeasurable fun A : Matrix (Fin M) (Fin N) ℝ => ∫ y,
      cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt) ∂ν :=
  StronglyMeasurable.integral_prod_left
    (f := fun y (A : Matrix (Fin M) (Fin N) ℝ) =>
      cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt))
    (cII_continuous_TP hSig hz v i μ ns ws σs cs Kt).measurable.stronglyMeasurable

private theorem cII_gg_le {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) (i : Fin M) (μ : Fin N) {p : ℕ}
    (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
    (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ) :
    ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
        ∂(colLaw X μ)‖ ≤
      cII_cT Kt p * cII_KW τ⁻¹ C (2 * ((3 * Kt + 4) * (p + 3))) *
        cII_U τ c A ^ ((3 * Kt + 4) * (p + 3)) := by
  have hF := cII_facts hset hz
  set n := (3 * Kt + 4) * (p + 3) with hn
  obtain ⟨hWi, hWle⟩ := cII_colLaw_moment hF.pos hX hF.N1 hF.Mle μ (2 * n)
  have hU0 := cII_U_nonneg hF A
  have hcT := cII_cT_one Kt p
  have hpt : ∀ y, ‖cII_T Sig (updCol A μ y) z v i μ ns ws σs cs
      (cII_P Sig (updCol A μ y) z μ Kt)‖ ≤
      cII_cT Kt p * cII_U τ c A ^ n * (1 + ∑ j, y j ^ 2) ^ (2 * n) := by
    intro y
    refine ((cII_TT_TP_le hset hz (updCol A μ y) hv i μ ns ws σs cs hns Kt).2).trans ?_
    have h1 := cII_U_updCol hF A μ y
    have h2 : cII_U τ c (updCol A μ y) ^ n ≤ (cII_U τ c A * cII_W y ^ 2) ^ n :=
      pow_le_pow_left₀ (cII_U_nonneg hF _) h1 n
    calc cII_cT Kt p * cII_U τ c (updCol A μ y) ^ n
        ≤ cII_cT Kt p * (cII_U τ c A * cII_W y ^ 2) ^ n :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = _ := by unfold cII_W; rw [mul_pow, ← pow_mul, mul_comm 2 n]; ring
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y, ‖cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)‖
        ∂(colLaw X μ)
      ≤ ∫ y, cII_cT Kt p * cII_U τ c A ^ n * (1 + ∑ j, y j ^ 2) ^ (2 * n) ∂(colLaw X μ) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hWi.const_mul _)
          (ae_of_all _ hpt)
    _ = cII_cT Kt p * cII_U τ c A ^ n * ∫ y, (1 + ∑ j, y j ^ 2) ^ (2 * n) ∂(colLaw X μ) :=
        integral_const_mul _ _
    _ ≤ cII_cT Kt p * cII_U τ c A ^ n * cII_KW τ⁻¹ C (2 * n) :=
        mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = _ := by ring

end ColAvg

/-! ## The expectation of one term -/

section OneTerm

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_int_TT {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ) :
    Integrable (fun ω =>
        cII_T Sig (X ω) z v i μ ns ws σs cs (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ))) ∧
      Integrable (fun ω => cII_T Sig (X ω) z v i μ ns ws σs cs (cII_P Sig (X ω) z μ Kt)) := by
  have hF := cII_facts hset hz
  have hXm := cII_measurable_X hX
  have hSig := hF.posDef
  have hη := hF.im_pos
  constructor
  · exact cII_integrable_U hX hF
      (f := fun A => cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)))
      ((cII_continuous_T hSig hη v i μ ns ws σs cs (cII_continuous_Gmumu hSig hη μ)).measurable.comp
        hXm).aestronglyMeasurable
      (fun A => (cII_TT_TP_le hset hz A hv i μ ns ws σs cs hns Kt).1)
  · exact cII_integrable_U hX hF
      (f := fun A => cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt))
      ((cII_continuous_T hSig hη v i μ ns ws σs cs (cII_continuous_P hSig hη μ Kt)).measurable.comp
        hXm).aestronglyMeasurable
      (fun A => (cII_TT_TP_le hset hz A hv i μ ns ws σs cs hns Kt).2)

/-- `|E v̄(μ)^{d_v} T(G_μμ)| ≤ |v̄(μ)|^{d_v} (E|T(G_μμ) − T(P_μ)| + E|E_μ T(P_μ)|)`. -/
private theorem cII_term_le {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ) :
    ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs * ∏ r, conjIf (cs r)
        (tagA Sig (X ω) z v i μ (ns r) (ws r) (σs r) *
          G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤
      |vbar Sig v (Sum.inr μ)| ^ dVof σs *
        ((∫ ω, ‖cII_T Sig (X ω) z v i μ ns ws σs cs (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)) -
            cII_T Sig (X ω) z v i μ ns ws σs cs (cII_P Sig (X ω) z μ Kt)‖) +
          ∫ ω, ‖∫ y, cII_T Sig (updCol (X ω) μ y) z v i μ ns ws σs cs
            (cII_P Sig (updCol (X ω) μ y) z μ Kt) ∂(colLaw X μ)‖) := by
  have hF := cII_facts hset hz
  obtain ⟨hTT, hTP⟩ := cII_int_TT hX hset hz hv i μ ns ws σs cs hns Kt
  have hcol := integral_colSplit hX μ
    (F := fun A => cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt))
    (cII_continuous_T hF.posDef hF.im_pos v i μ ns ws σs cs
      (cII_continuous_P hF.posDef hF.im_pos μ Kt)).measurable hTP
  change ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs *
    cII_T Sig (X ω) z v i μ ns ws σs cs (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ))‖ ≤ _
  rw [integral_const_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e2 : ∫ ω, cII_T Sig (X ω) z v i μ ns ws σs cs (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)) =
      (∫ ω, (cII_T Sig (X ω) z v i μ ns ws σs cs (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)) -
        cII_T Sig (X ω) z v i μ ns ws σs cs (cII_P Sig (X ω) z μ Kt))) +
      ∫ ω, cII_T Sig (X ω) z v i μ ns ws σs cs (cII_P Sig (X ω) z μ Kt) := by
    rw [integral_sub hTT hTP]; ring
  rw [e2, hcol]
  refine (norm_add_le _ _).trans (add_le_add (norm_integral_le_integral_norm _)
    (norm_integral_le_integral_norm _))

end OneTerm

/-! ## The bound on `Θ` -/

section OnTheta

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

/-- The random variable `Z = N^{−3/2} ∑_{iμ} |v̄(μ)|^{d_v} (|T(G_μμ) − T(P_μ)| + |E_μ T(P_μ)|)`. -/
private def cII_Z (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (Kt : ℕ)
    (ν : Fin N → Measure (Fin M → ℝ)) : ℝ :=
  (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ, |vbar Sig v (Sum.inr μ)| ^ dVof σs *
    (‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
        cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
      ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
        ∂(ν μ)‖)

/-- The dominating variable `F = ∑_μ (c₈ w'_μ + N⁻¹)(B^p + a_μ^p)`. -/
private def cII_Fb (Sig : Matrix (Fin M) (Fin M) ℝ) (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ)
    (v : Fin M ⊕ Fin N → ℝ) (p dv : ℕ) (c8 Km K b B : ℝ) : ℝ :=
  ∑ μ, (c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) + (N : ℝ)⁻¹) *
    (B ^ p + cII_a Sig A z v μ Km K b ^ p)

private theorem cII_onTheta {K b Cn Kmax : ℝ} {S : Set ℂ} (hset : CompSetting τ c M N Sig S)
    (hz : z ∈ S) {A : Matrix (Fin M) (Fin N) ℝ} {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ 1) (hbN : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b)
    (hΘ : ∀ μ, GoodSec8 τ K b Cn Sig A z v μ) {p : ℕ} (hp : 0 < p) (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (Kt : ℕ)
    (hB : K ^ (15 * Kt + 24) * b ≤ 1) (hKmax : 0 ≤ Kmax)
    (hε : K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) ≤ K)
    (hrep : τ⁻¹ * (N : ℝ) ^ 2 * (p + 3) * (K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1)) *
      (2 * K) ^ 12 ≤ 1) (ν : Fin N → Measure (Fin M → ℝ))
    (hint : ∀ (μ : Fin N) (i : Fin M) (k : ℕ) (ct : Fin k → Bool), Integrable (fun y : Fin M → ℝ =>
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ)) (ν μ))
    (hL : ∀ (μ : Fin N) (i : Fin M) (k : ℕ) (ct : Fin k → Bool), k ≤ Kt * dMuof σs → ‖∫ y,
      (∏ r, conjIf (cs r) (((tagForms Sig A z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol A μ y) z μ) ∂(ν μ)‖ ≤
        Kmax * K ^ (dXof ns ws σs + Kt * dMuof σs) *
          (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
              b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0)
            else b ^ dXof ns ws σs)) :
    cII_Z Sig A z v ns ws σs cs Kt ν ≤
      cII_Fb Sig A z v p (dVof σs) (2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax) (mBoundConst τ) K b
        (K ^ (15 * Kt + 24) * b) := by
  have hF := cII_facts hset hz
  have hN := hF.N1
  have hm : ∀ μ : Fin N, ‖PiZ N Sig z (Sum.inr μ) (Sum.inr μ)‖ ≤ mBoundConst τ := fun μ => by
    rw [cII_PiZ_mu]; exact hF.m_le
  have hv' : ∀ μ : Fin N, |vbar Sig v (Sum.inr μ)| ≤ 1 := fun μ => cII_vbar_inr_le hv μ
  unfold cII_Z cII_Fb
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  have hrepμ := cII_mu_rep hF.pos hF.posDef hF.im_pos hN hK hb0 hb hbN hF.Km1 (hv' μ) (hm μ)
    hF.Mle (hΘ μ) ns ws σs cs hns Kt hε hrep
  have hmainμ := cII_mu_main hF.pos hF.le_one hF.posDef hF.im_pos hN hK hb0 hb hbN hF.Km1 (hv' μ)
    (hm μ) hF.Mle (hΘ μ) hp ns ws σs cs hns hnz Kt hB hKmax (ν μ) (hint μ) (hL μ)
  have e : (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, |vbar Sig v (Sum.inr μ)| ^ dVof σs *
      (‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(ν μ)‖) =
      (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dVof σs * ∑ i,
        ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖) +
      (N : ℝ) ^ (-(3 : ℝ) / 2) * (|vbar Sig v (Sum.inr μ)| ^ dVof σs * ∑ i,
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(ν μ)‖) := by
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  rw [e]
  have hw0 := cII_w_nonneg N (dVof σs) (vbar Sig v (Sum.inr μ))
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ cII_a Sig A z v μ (mBoundConst τ) K b :=
    cII_a_nonneg (by linarith [hF.Km1]) hK0 hb0
  have hBp : 0 ≤ (K ^ (15 * Kt + 24) * b) ^ p := by positivity
  have hNi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  nlinarith [mul_nonneg hNi hBp]

end OnTheta

/-! ## Expectations -/

section Expect

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_colLaw_sfinite {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (μ : Fin N) : SFinite (colLaw X μ) := by
  have : ∀ j, IsProbabilityMeasure (entryLaw X (j, μ)) := fun j => by
    unfold entryLaw; infer_instance
  unfold colLaw; infer_instance

private theorem cII_int_parts {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (i : Fin M) (μ : Fin N) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ) :
    Integrable (fun ω =>
        ‖cII_T Sig (X ω) z v i μ ns ws σs cs (G Sig (X ω) z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig (X ω) z v i μ ns ws σs cs (cII_P Sig (X ω) z μ Kt)‖) ∧
      Integrable (fun ω => ‖∫ y, cII_T Sig (updCol (X ω) μ y) z v i μ ns ws σs cs
        (cII_P Sig (updCol (X ω) μ y) z μ Kt) ∂(colLaw X μ)‖) := by
  have hF := cII_facts hset hz
  obtain ⟨hTT, hTP⟩ := cII_int_TT hX hset hz hv i μ ns ws σs cs hns Kt
  refine ⟨(hTT.sub hTP).norm, ?_⟩
  have := cII_colLaw_sfinite X μ
  have hm := (cII_gg_meas hF.posDef hF.im_pos v i μ ns ws σs cs Kt (colLaw X μ)).measurable.comp
    (cII_measurable_X hX)
  exact (cII_integrable_U hX hF hm.aestronglyMeasurable
    (fun A => cII_gg_le hX hset hz A hv i μ ns ws σs cs hns Kt)).norm

/-- `N^{−3/2} ∑_{iμ} |E v̄(μ)^{d_v} T(G_μμ)| ≤ E Z`. -/
private theorem cII_LHS_le {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
        ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs * ∏ r, conjIf (cs r)
          (tagA Sig (X ω) z v i μ (ns r) (ws r) (σs r) *
            G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤
      ∫ ω, cII_Z Sig (X ω) z v ns ws σs cs Kt (fun μ => colLaw X μ) := by
  have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hI := fun i μ => cII_int_parts hX hset hz hv i μ ns ws σs cs hns Kt
  unfold cII_Z
  dsimp only
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ hNp
  rw [integral_finsetSum]
  · refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_le_sum fun μ _ => ?_
      refine (cII_term_le hX hset hz hv i μ ns ws σs cs hns Kt).trans (le_of_eq ?_)
      rw [integral_const_mul, integral_add (hI i μ).1 (hI i μ).2]
    · intro μ _
      exact ((hI i μ).1.add (hI i μ).2).const_mul _
  · intro i _
    exact integrable_finsetSum _ fun μ _ => ((hI i μ).1.add (hI i μ).2).const_mul _

end Expect

section Expect2

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

/-- `Z ≤ τ⁻¹ N c_T (2 + c_W) U^{n_U}`. -/
private theorem cII_Z_le {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (hns : ∑ r, ns r = 3) (Kt : ℕ)
    (A : Matrix (Fin M) (Fin N) ℝ) :
    cII_Z Sig A z v ns ws σs cs Kt (fun μ => colLaw X μ) ≤
      τ⁻¹ * N * (cII_cT Kt p * (2 + cII_KW τ⁻¹ C (2 * ((3 * Kt + 4) * (p + 3))))) *
        cII_U τ c A ^ ((3 * Kt + 4) * (p + 3)) := by
  have hF := cII_facts hset hz
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hF.N1
  have hNp : (0 : ℝ) < N := by linarith
  set n := (3 * Kt + 4) * (p + 3) with hn
  set cW := cII_KW τ⁻¹ C (2 * n) with hcW
  have hcW0 : 0 ≤ cW := cII_KW_nonneg (inv_pos.2 hF.pos).le C _
  have hU0 := cII_U_nonneg hF A
  have hcT := cII_cT_one Kt p
  have hterm : ∀ i μ, |vbar Sig v (Sum.inr μ)| ^ dVof σs *
      (‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(colLaw X μ)‖) ≤ cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n := by
    intro i μ
    have hvd : |vbar Sig v (Sum.inr μ)| ^ dVof σs ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (cII_vbar_inr_le hv μ)
    obtain ⟨h1, h2⟩ := cII_TT_TP_le hset hz A hv i μ ns ws σs cs hns Kt
    have h3 := cII_gg_le hX hset hz A hv i μ ns ws σs cs hns Kt
    have h4 := norm_sub_le (cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)))
      (cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt))
    have h5 : 0 ≤ ‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(colLaw X μ)‖ := by positivity
    calc _ ≤ 1 * (‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(colLaw X μ)‖) := mul_le_mul_of_nonneg_right hvd h5
      _ ≤ _ := by nlinarith
  unfold cII_Z
  dsimp only
  have hpre : (N : ℝ) ^ (-(3 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hpre0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hNp.le _
  have hsum : ∑ i, ∑ μ, |vbar Sig v (Sum.inr μ)| ^ dVof σs *
      (‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(colLaw X μ)‖) ≤ M * N * (cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n) := by
    calc _ ≤ ∑ _i : Fin M, ∑ _μ : Fin N, cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun μ _ => hterm i μ
      _ = _ := by simp; ring
  have hS0 : 0 ≤ ∑ i, ∑ μ, |vbar Sig v (Sum.inr μ)| ^ dVof σs *
      (‖cII_T Sig A z v i μ ns ws σs cs (G Sig A z (Sum.inr μ) (Sum.inr μ)) -
          cII_T Sig A z v i μ ns ws σs cs (cII_P Sig A z μ Kt)‖ +
        ‖∫ y, cII_T Sig (updCol A μ y) z v i μ ns ws σs cs (cII_P Sig (updCol A μ y) z μ Kt)
          ∂(colLaw X μ)‖) := by positivity
  have hpre' : (N : ℝ) ^ (-(3 : ℝ) / 2) * N ≤ 1 := by
    rw [cII_rpow_three_half hF.N1]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hc0 : 0 ≤ cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n := by positivity
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * _ ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) *
        (M * N * (cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n)) :=
        mul_le_mul_of_nonneg_left hsum hpre0
    _ = ((N : ℝ) ^ (-(3 : ℝ) / 2) * N) * M * (cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n) := by ring
    _ ≤ 1 * (τ⁻¹ * N) * (cII_cT Kt p * (2 + cW) * cII_U τ c A ^ n) := by
        gcongr
        exact hF.Mle
    _ = _ := by ring

/-- `E U(X)^m ≤ c_U^m N^{2m} 2^{2m}(1 + τ^{−2m} C'_{4m}) N^{2m}`. -/
private theorem cII_int_U_le {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    (hF : cII_Facts (N := N) τ c Sig z) (m : ℕ) :
    ∫ ω, cII_U τ c (X ω) ^ m ≤ cII_cU τ c ^ m * cII_KW τ⁻¹ C (2 * m) * (N : ℝ) ^ (4 * m) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hF.N1
  obtain ⟨hWi, hWle⟩ := cII_moment_W hF.pos hX hF.N1 hF.Mle (2 * m)
  have hKW : cII_KW (τ⁻¹ * N) C (2 * m) ≤ cII_KW τ⁻¹ C (2 * m) * (N : ℝ) ^ (2 * m) := by
    unfold cII_KW
    have h0 : 0 ≤ max (C (2 * (2 * m))) 0 := le_max_right _ _
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * m) := one_le_pow₀ hN
    have hτ0 : 0 ≤ τ⁻¹ := (inv_pos.2 hF.pos).le
    rw [mul_pow]
    have h3 : (2 : ℝ) ^ (2 * m) ≤ 2 ^ (2 * m) * (N : ℝ) ^ (2 * m) :=
      le_mul_of_one_le_right (by positivity) h1
    calc (2 : ℝ) ^ (2 * m) * (1 + τ⁻¹ ^ (2 * m) * (N : ℝ) ^ (2 * m) * max (C (2 * (2 * m))) 0)
        = 2 ^ (2 * m) + 2 ^ (2 * m) * (τ⁻¹ ^ (2 * m) * max (C (2 * (2 * m))) 0) *
            (N : ℝ) ^ (2 * m) := by ring
      _ ≤ 2 ^ (2 * m) * (N : ℝ) ^ (2 * m) + 2 ^ (2 * m) *
            (τ⁻¹ ^ (2 * m) * max (C (2 * (2 * m))) 0) * (N : ℝ) ^ (2 * m) := by linarith
      _ = _ := by ring
  have hc : 0 ≤ cII_cU τ c := by
    unfold cII_cU; have := hF.rough1; have := hF.Km1; have := hF.pos; positivity
  have e : ∀ ω, cII_U τ c (X ω) ^ m = (cII_cU τ c ^ m * (N : ℝ) ^ (2 * m)) *
      (1 + cII_sq (X ω)) ^ (2 * m) := fun ω => by
    unfold cII_U; rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  simp_rw [e]
  rw [integral_const_mul]
  calc cII_cU τ c ^ m * (N : ℝ) ^ (2 * m) * ∫ ω, (1 + cII_sq (X ω)) ^ (2 * m)
      ≤ cII_cU τ c ^ m * (N : ℝ) ^ (2 * m) * (cII_KW τ⁻¹ C (2 * m) * (N : ℝ) ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left (hWle.trans hKW) (by positivity)
    _ = _ := by rw [show 4 * m = 2 * m + 2 * m by ring, pow_add]; ring

end Expect2

section Expect3

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_pow3_le {x y w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (p : ℕ) :
    (x + y + w) ^ p ≤ 3 ^ p * (x ^ p + y ^ p + w ^ p) := by
  set m := max x (max y w) with hm
  have hxm : x ≤ m := le_max_left _ _
  have hym : y ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hwm : w ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have h1 : (x + y + w) ^ p ≤ (3 * m) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
  have h2 : m ^ p ≤ x ^ p + y ^ p + w ^ p := by
    have hxp := pow_nonneg hx p
    have hyp := pow_nonneg hy p
    have hwp := pow_nonneg hw p
    rcases max_choice x (max y w) with h | h <;> rw [← hm] at h
    · rw [h]; linarith
    · rcases max_choice y w with h' | h' <;> rw [h'] at h <;> rw [h] <;> linarith
  calc (x + y + w) ^ p ≤ (3 * m) ^ p := h1
    _ = 3 ^ p * m ^ p := mul_pow _ _ _
    _ ≤ 3 ^ p * (x ^ p + y ^ p + w ^ p) := mul_le_mul_of_nonneg_left h2 (by positivity)

private theorem cII_maxFp_ge {Ω : Type*} [MeasureSpace Ω] (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (p : ℕ)
    (w : Option (Fin N)) : ∫ ω, Fv Sig (X ω) z (vfam v w) ^ p ≤ maxFp Sig X z v p := by
  unfold maxFp
  exact le_ciSup (Finite.bddAbove_range (fun w => ∫ ω, Fv Sig (X ω) z (vfam v w) ^ p)) w

private theorem cII_maxFp_nonneg {Ω : Type*} [MeasureSpace Ω] (Sig : Matrix (Fin M) (Fin M) ℝ)
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (v : Fin M ⊕ Fin N → ℝ) (p : ℕ) :
    0 ≤ maxFp Sig X z v p :=
  (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) p).trans (cII_maxFp_ge Sig X z v p none)

private theorem cII_int_Fv {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {w : Fin M ⊕ Fin N → ℝ} (hw : testNorm w = 1)
    (p : ℕ) : Integrable fun ω => Fv Sig (X ω) z w ^ p := by
  have hF := cII_facts hset hz
  refine cII_integrable_U hX hF (f := fun A => Fv Sig A z w ^ p)
    ((((cII_continuous_Fv hF.posDef hF.im_pos w).pow p).measurable.comp
      (cII_measurable_X hX)).aestronglyMeasurable) (cf := 1) (n := p) fun A => ?_
  rw [Real.norm_of_nonneg (pow_nonneg (show 0 ≤ Fv Sig A z w from norm_nonneg _) _), one_mul]
  refine pow_le_pow_left₀ (norm_nonneg _) ((cII_Fv_le hset hz A hw).trans (cII_U_ge_mul hF A ?_)) p
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hF.pos).2 hF.le_one
  have h3 : 1 ≤ τ⁻¹ ^ 3 := one_le_pow₀ hT
  nlinarith [hF.rough1, hF.Km1]

/-- `E a_μ^p ≤ (12 K_m)^p ((K b)^p + 2 max_{𝒱_v} E F^p)`. -/
private theorem cII_int_a {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (μ : Fin N) (p : ℕ) {K b : ℝ} (hK0 : 0 ≤ K) (hb0 : 0 ≤ b) :
    Integrable (fun ω => cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p) ∧
      ∫ ω, cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p ≤
        (12 * mBoundConst τ) ^ p * ((K * b) ^ p + 2 * maxFp Sig X z v p) := by
  have hF := cII_facts hset hz
  have hKm := hF.Km1
  have h1 := cII_int_Fv hX hset hz hv p
  have h2 := cII_int_Fv hX hset hz (w := eI (Sum.inr μ)) (cII_testNorm_eI _) p
  have hpt : ∀ ω, cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p ≤
      (12 * mBoundConst τ) ^ p * ((K * b) ^ p + Fv Sig (X ω) z v ^ p +
        Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p) := by
    intro ω
    unfold cII_a
    rw [mul_pow, show (12 * mBoundConst τ) ^ p = (4 * mBoundConst τ) ^ p * 3 ^ p by
      rw [← mul_pow]; ring_nf, mul_assoc]
    exact mul_le_mul_of_nonneg_left (cII_pow3_le (by positivity) (norm_nonneg _) (norm_nonneg _) p)
      (by positivity)
  have hmeas : Measurable fun ω => cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p := by
    unfold cII_a
    exact ((measurable_const.mul ((measurable_const.add
      ((cII_continuous_Fv hF.posDef hF.im_pos v).measurable.comp (cII_measurable_X hX))).add
      ((cII_continuous_Fv hF.posDef hF.im_pos _).measurable.comp
        (cII_measurable_X hX))))).pow_const p
  have hint : Integrable fun ω => (12 * mBoundConst τ) ^ p * ((K * b) ^ p + Fv Sig (X ω) z v ^ p +
      Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p) :=
    (((integrable_const _).add h1).add h2).const_mul _
  have hia : Integrable fun ω => cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p :=
    hint.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (cII_a_nonneg (by linarith) hK0 hb0) _)]
      exact hpt ω)
  refine ⟨hia, ?_⟩
  have hv1 := cII_maxFp_ge Sig X z v p none
  have hv2 := cII_maxFp_ge Sig X z v p (some μ)
  simp only [vfam] at hv1 hv2
  calc ∫ ω, cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p
      ≤ ∫ ω, (12 * mBoundConst τ) ^ p * ((K * b) ^ p + Fv Sig (X ω) z v ^ p +
          Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p) := integral_mono hia hint hpt
    _ = (12 * mBoundConst τ) ^ p * ((K * b) ^ p + (∫ ω, Fv Sig (X ω) z v ^ p) +
          ∫ ω, Fv Sig (X ω) z (eI (Sum.inr μ)) ^ p) := by
        rw [integral_const_mul, integral_add ?_ h2, integral_add (integrable_const _) h1]
        · simp
        · exact (integrable_const _).add h1
    _ ≤ (12 * mBoundConst τ) ^ p * ((K * b) ^ p + 2 * maxFp Sig X z v p) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

end Expect3

section Expect4

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_int_Fb {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hz : z ∈ S) {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1)
    (p dv : ℕ) {c8 K b B : ℝ} (hc8 : 0 ≤ c8) (hK0 : 0 ≤ K) (hb0 : 0 ≤ b) (hB : 0 ≤ B) :
    Integrable (fun ω => cII_Fb Sig (X ω) z v p dv c8 (mBoundConst τ) K b B) ∧
      ∫ ω, cII_Fb Sig (X ω) z v p dv c8 (mBoundConst τ) K b B ≤
        (c8 + 1) * (B ^ p + (12 * mBoundConst τ) ^ p * ((K * b) ^ p + 2 * maxFp Sig X z v p)) := by
  have hF := cII_facts hset hz
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hF.N1
  have hNp : (0 : ℝ) < N := by linarith
  have ha := fun μ => cII_int_a hX hset hz hv μ p hK0 hb0
  set Λ := (12 * mBoundConst τ) ^ p * ((K * b) ^ p + 2 * maxFp Sig X z v p) with hΛ
  have hw : ∀ μ : Fin N, 0 ≤ c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) + (N : ℝ)⁻¹ := fun μ => by
    have := cII_w_nonneg N dv (vbar Sig v (Sum.inr μ)); positivity
  have hI : ∀ μ : Fin N, Integrable fun ω => (c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) +
      (N : ℝ)⁻¹) * (B ^ p + cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p) := fun μ =>
    ((integrable_const _).add (ha μ).1).const_mul _
  unfold cII_Fb
  refine ⟨integrable_finsetSum _ fun μ _ => hI μ, ?_⟩
  rw [integral_finsetSum _ fun μ _ => hI μ]
  have hsw : ∑ μ : Fin N, (c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) + (N : ℝ)⁻¹) ≤ c8 + 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := cII_w_sum (Sig := Sig) hv hF.N1 dv
    have h2 : ∑ _μ : Fin N, (N : ℝ)⁻¹ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ hNp.ne'
    rw [h2]
    nlinarith
  have hΛ0 : 0 ≤ B ^ p + Λ := by
    have := cII_maxFp_nonneg Sig X z v p
    have := hF.Km1
    positivity
  calc ∑ μ, ∫ ω, (c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) + (N : ℝ)⁻¹) *
        (B ^ p + cII_a Sig (X ω) z v μ (mBoundConst τ) K b ^ p)
      ≤ ∑ μ : Fin N, (c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) + (N : ℝ)⁻¹) * (B ^ p + Λ) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        rw [integral_const_mul, integral_add (integrable_const _) (ha μ).1]
        refine mul_le_mul_of_nonneg_left ?_ (hw μ)
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        linarith [(ha μ).2]
    _ = (∑ μ : Fin N, (c8 * cII_w N dv (vbar Sig v (Sum.inr μ)) + (N : ℝ)⁻¹)) * (B ^ p + Λ) := by
        rw [Finset.sum_mul]
    _ ≤ (c8 + 1) * (B ^ p + Λ) := mul_le_mul_of_nonneg_right hsw hΛ0

end Expect4

/-! ## The parameters and the eventual inequalities -/

section Numerics

/-- `C N^r ≤ N^s` for all large `N` when `r < s`. -/
private theorem cII_eventually (C r s : ℝ) (hrs : r < s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C * (N : ℝ) ^ r ≤ (N : ℝ) ^ s := by
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  refine ⟨⌈C' ^ (s - r)⁻¹⌉₊ + 1, fun N hN => ?_⟩
  have hsr : 0 < s - r := by linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
    exact_mod_cast this
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : C' ^ (s - r)⁻¹ ≤ (N : ℝ) := by
    have := Nat.le_ceil (C' ^ (s - r)⁻¹)
    have h2 : (⌈C' ^ (s - r)⁻¹⌉₊ : ℝ) ≤ N := by
      have : ⌈C' ^ (s - r)⁻¹⌉₊ ≤ N := by omega
      exact_mod_cast this
    linarith
  have h3 : C' ≤ (N : ℝ) ^ (s - r) := by
    calc C' = (C' ^ (s - r)⁻¹) ^ (s - r) :=
          (Real.rpow_inv_rpow (by linarith) hsr.ne').symm
      _ ≤ (N : ℝ) ^ (s - r) := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 hsr.le
  have h4 : 0 ≤ (N : ℝ) ^ r := Real.rpow_nonneg hNp.le _
  calc C * (N : ℝ) ^ r ≤ C' * (N : ℝ) ^ r := mul_le_mul_of_nonneg_right (le_max_left _ _) h4
    _ ≤ (N : ℝ) ^ (s - r) * (N : ℝ) ^ r := mul_le_mul_of_nonneg_right h3 h4
    _ = (N : ℝ) ^ s := by rw [← Real.rpow_add hNp]; ring_nf

private theorem cII_eventually0 (C s : ℝ) (hs : 0 < s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ (N : ℝ) ^ s := by
  obtain ⟨N₀, h⟩ := cII_eventually C 0 s hs
  refine ⟨N₀, fun N hN => ?_⟩
  have := h N hN
  rwa [Real.rpow_zero, mul_one] at this

/-- `Ψ` from below and above on `𝐃(τ, N)`: `N^{−1/2} ≤ √K_m Ψ`, `Ψ ≤ (√K_m + 1) N^{−τ/2}`,
`Ψ ≥ τ/N`. -/
private theorem cII_Psi_bounds {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) :
    (Real.sqrt N)⁻¹ ≤ Real.sqrt (mBoundConst τ) * Psi N (specOf Sig) z ∧
      Psi N (specOf Sig) z ≤ (Real.sqrt (mBoundConst τ) + 1) * (N : ℝ) ^ (-(τ / 2)) ∧
      τ / N ≤ Psi N (specOf Sig) z := by
  have hN := cII_N_pos hset
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hτ := hset.pos
  have hzD := hset.domain.1 hz
  have hη : 0 < z.im := hzD.1
  have hηt : z.im ≤ τ⁻¹ := hzD.2.2.2.2
  obtain ⟨-, hmK, hmI⟩ := gen_prop_m_specDomain (cII_density hset) hzD
  set Km := mBoundConst τ with hKm
  have hKm0 : 0 < Km := by rw [hKm]; unfold mBoundConst genPropConst; positivity
  set m := mFun N (specOf Sig) z with hm
  have hNη : 0 < (N : ℝ) * z.im := by positivity
  have hNη1 := cII_one_le_N_im hN hτ hzD
  have hNτ : (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [mul_comm, ← Real.rpow_add_one hNp.ne']; ring_nf
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hzD.2.2.2.1 hNp.le
  have hNτ0 : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNp _
  have hP0 : 0 ≤ Real.sqrt (m.im / (N * z.im)) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold Psi
    have hq : Km⁻¹ * (N : ℝ)⁻¹ ≤ m.im / (N * z.im) := by
      rw [le_div_iff₀ hNη]
      calc Km⁻¹ * (N : ℝ)⁻¹ * (N * z.im) = Km⁻¹ * z.im := by field_simp
        _ ≤ m.im := hmI
    have hs := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (inv_nonneg.2 hKm0.le), Real.sqrt_inv, Real.sqrt_inv] at hs
    have hsK : 0 < Real.sqrt Km := Real.sqrt_pos.2 hKm0
    have h1 : (Real.sqrt N)⁻¹ ≤ Real.sqrt Km * Real.sqrt (m.im / (N * z.im)) := by
      have := mul_le_mul_of_nonneg_left hs hsK.le
      rwa [← mul_assoc, mul_inv_cancel₀ hsK.ne', one_mul] at this
    have h2 : 0 ≤ Real.sqrt Km * (1 / (N * z.im)) := by positivity
    linarith [mul_add (Real.sqrt Km) (Real.sqrt (m.im / (N * z.im))) (1 / (N * z.im))]
  · unfold Psi
    have hmI' : m.im ≤ Km := (Complex.im_le_norm m).trans hmK
    have hsqτ : Real.sqrt ((N : ℝ) ^ τ) = (N : ℝ) ^ (τ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]; ring_nf
    have hneg : (N : ℝ) ^ (-(τ / 2)) = ((N : ℝ) ^ (τ / 2))⁻¹ := Real.rpow_neg hNp.le _
    have hh0 : 0 < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNp _
    have hh1 : 1 ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1r (by linarith)
    have hsq : Real.sqrt (m.im / (N * z.im)) ≤ Real.sqrt Km * ((N : ℝ) ^ (τ / 2))⁻¹ := by
      have : m.im / (N * z.im) ≤ Km / (N : ℝ) ^ τ := by
        calc m.im / (N * z.im) ≤ Km / (N * z.im) :=
              div_le_div_of_nonneg_right hmI' hNη.le
          _ ≤ Km / (N : ℝ) ^ τ := div_le_div_of_nonneg_left hKm0.le hNτ0 hNτ
      calc _ ≤ Real.sqrt (Km / (N : ℝ) ^ τ) := Real.sqrt_le_sqrt this
        _ = Real.sqrt Km * ((N : ℝ) ^ (τ / 2))⁻¹ := by
            rw [Real.sqrt_div' _ hNτ0.le, hsqτ, div_eq_mul_inv]
    have h1 : 1 / ((N : ℝ) * z.im) ≤ ((N : ℝ) ^ (τ / 2))⁻¹ := by
      rw [one_div]
      refine inv_anti₀ hh0 ?_
      have : (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ :=
        Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      linarith
    rw [hneg]
    nlinarith
  · unfold Psi
    have h1 : τ / N ≤ 1 / (N * z.im) := by
      rw [div_le_div_iff₀ hNp hNη, one_mul]
      calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
        _ = N := by field_simp
    linarith

/-- The parameter facts at `C₀(τ) ≤ C₀`, `C₀δ ≤ τ/4`: `2400 ≤ C₀`, `K_τ ≥ 24/τ`,
`45 K_τ + 75 ≤ C₀/2`, `6δ ≤ τ/4`, `39 δ ≤ 1`. -/
private theorem cII_params {τ C₀ δ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ)
    (hC₀ : czero τ ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    2400 ≤ C₀ ∧ 24 / τ ≤ (kTau τ : ℝ) ∧ 45 * (kTau τ : ℝ) + 75 ≤ C₀ / 2 ∧ 6 * δ ≤ τ / 4 ∧
      39 * δ ≤ 1 := by
  have h1 : (kTau τ : ℝ) < 24 / τ + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1' : 24 / τ ≤ (kTau τ : ℝ) := Nat.le_ceil _
  have h2 : 2400 / τ ≤ czero τ := Nat.le_ceil _
  have h3 : 1 ≤ τ⁻¹ := one_le_inv_iff₀.mpr ⟨hτ, hτ1⟩
  have h4 : 2400 ≤ 2400 / τ := by rw [le_div_iff₀ hτ]; nlinarith
  have hC : 2400 ≤ C₀ := by linarith
  refine ⟨hC, h1', ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv] at h1 h2
    linarith
  · nlinarith
  · nlinarith

end Numerics

section Numerics2

private theorem cII_rep_num {n τ δ : ℝ} {Kt p : ℕ} (hn : 1 ≤ n) (hτ : 0 < τ) (hδ : 0 < δ)
    (hKt : 24 / τ ≤ (Kt : ℝ)) (h6 : 6 * δ ≤ τ / 4) (h39 : 39 * δ ≤ 1) (h2 : 2 ≤ n ^ (τ / 4))
    (hc : τ⁻¹ * (p + 3) * 2 ^ 12 * 2 ^ (Kt + 1) ≤ n) :
    n ^ (3 * δ) * (n ^ (3 * δ) * n ^ (-τ / 2) * (2 * n ^ (3 * δ))) ^ (Kt + 1) ≤ n ^ (3 * δ) ∧
      τ⁻¹ * n ^ 2 * (p + 3) *
        (n ^ (3 * δ) * (n ^ (3 * δ) * n ^ (-τ / 2) * (2 * n ^ (3 * δ))) ^ (Kt + 1)) *
          (2 * n ^ (3 * δ)) ^ 12 ≤ 1 := by
  have hn0 : 0 < n := by linarith
  have hK0 : 0 < n ^ (3 * δ) := Real.rpow_pos_of_pos hn0 _
  set K := n ^ (3 * δ) with hK
  have hq0 : 0 < n ^ (τ / 4) := Real.rpow_pos_of_pos hn0 _
  -- `ρ = K N^{−τ/2} (2K) ≤ 2 N^{−τ/4} ≤ 1`
  have hρ : K * n ^ (-τ / 2) * (2 * K) ≤ 2 * (n ^ (τ / 4))⁻¹ := by
    have e : K * n ^ (-τ / 2) * (2 * K) = 2 * n ^ (6 * δ - τ / 2) := by
      rw [hK, show 6 * δ - τ / 2 = 3 * δ + (-τ / 2) + 3 * δ by ring, Real.rpow_add hn0,
        Real.rpow_add hn0]; ring
    rw [e, ← Real.rpow_neg hn0.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
      (by norm_num)
  have hρ0 : 0 ≤ K * n ^ (-τ / 2) * (2 * K) := by
    have := Real.rpow_nonneg hn0.le (-τ / 2); positivity
  have hρ1 : K * n ^ (-τ / 2) * (2 * K) ≤ 1 := by
    refine hρ.trans ?_
    rw [← div_eq_mul_inv, div_le_one hq0]; exact h2
  refine ⟨?_, ?_⟩
  · calc K * (K * n ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) ≤ K * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0 hρ1) hK0.le
      _ = K := mul_one K
  · have h1 : (K * n ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) ≤ 2 ^ (Kt + 1) * n ^ (-(6 : ℝ)) := by
      calc (K * n ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) ≤ (2 * (n ^ (τ / 4))⁻¹) ^ (Kt + 1) :=
            pow_le_pow_left₀ hρ0 hρ _
        _ = 2 ^ (Kt + 1) * n ^ (-(τ / 4 * ((Kt : ℝ) + 1))) := by
            rw [mul_pow, ← Real.rpow_neg hn0.le, ← Real.rpow_natCast (n ^ (-(τ / 4))) (Kt + 1),
              ← Real.rpow_mul hn0.le]
            push_cast; ring_nf
        _ ≤ 2 ^ (Kt + 1) * n ^ (-(6 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn ?_)
              (by positivity)
            have : 24 ≤ τ * Kt := by rwa [div_le_iff₀ hτ, mul_comm] at hKt
            nlinarith
    have h3 : K * (2 * K) ^ 12 ≤ 2 ^ 12 * n := by
      have e : K * (2 * K) ^ 12 = 2 ^ 12 * n ^ (39 * δ) := by
        rw [mul_pow, hK, ← Real.rpow_natCast (n ^ (3 * δ)), ← Real.rpow_mul hn0.le]
        rw [show (39 : ℝ) * δ = 3 * δ + 3 * δ * ((12 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_add hn0]
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc n ^ (39 * δ) ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn h39
        _ = n := Real.rpow_one n
    have h4 : n ^ 2 * n * n ^ (-(6 : ℝ)) ≤ n⁻¹ := by
      rw [show n ^ 2 * n = n ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]; ring,
        ← Real.rpow_add hn0, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    have hT : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
    have hp3 : (0 : ℝ) ≤ p + 3 := by positivity
    have hn6 : 0 ≤ n ^ (-(6 : ℝ)) := Real.rpow_nonneg hn0.le _
    calc τ⁻¹ * n ^ 2 * (p + 3) * (K * (K * n ^ (-τ / 2) * (2 * K)) ^ (Kt + 1)) * (2 * K) ^ 12
        = τ⁻¹ * n ^ 2 * (p + 3) * (K * (2 * K) ^ 12) * (K * n ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) := by
          ring
      _ ≤ τ⁻¹ * n ^ 2 * (p + 3) * (2 ^ 12 * n) * (2 ^ (Kt + 1) * n ^ (-(6 : ℝ))) := by
          gcongr
      _ = (τ⁻¹ * (p + 3) * 2 ^ 12 * 2 ^ (Kt + 1)) * (n ^ 2 * n * n ^ (-(6 : ℝ))) := by ring
      _ ≤ n * n⁻¹ := mul_le_mul hc h4 (by positivity) hn0.le
      _ = 1 := mul_inv_cancel₀ hn0.ne'

end Numerics2

/-! ## Measurability of `Z` and `F`; vanishing tagged words -/

section MeasZ

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_Z_meas {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → Matrix (Fin M) (Fin N) ℝ) (hSig : Sig.PosDef) (hz : 0 < z.im)
    (v : Fin M ⊕ Fin N → ℝ) {p : ℕ} (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r))
    (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool) (Kt : ℕ) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ => cII_Z Sig A z v ns ws σs cs Kt
      (fun μ => colLaw X μ) := by
  unfold cII_Z
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun μ _ => Measurable.const_mul (Measurable.add ?_ ?_) _) _
  · exact ((cII_continuous_T hSig hz v i μ ns ws σs cs (cII_continuous_Gmumu hSig hz μ)).sub
      (cII_continuous_T hSig hz v i μ ns ws σs cs (cII_continuous_P hSig hz μ Kt))).norm.measurable
  · have := cII_colLaw_sfinite X μ
    exact (cII_gg_meas hSig hz v i μ ns ws σs cs Kt (colLaw X μ)).measurable.norm

private theorem cII_Fb_meas (hSig : Sig.PosDef) (hz : 0 < z.im) (v : Fin M ⊕ Fin N → ℝ)
    (p dv : ℕ) (c8 Km K b B : ℝ) :
    Measurable fun A : Matrix (Fin M) (Fin N) ℝ => cII_Fb Sig A z v p dv c8 Km K b B := by
  unfold cII_Fb cII_a
  refine Finset.measurable_sum _ fun μ _ => Measurable.const_mul (measurable_const.add ?_) _
  exact ((measurable_const.mul ((measurable_const.add
    (cII_continuous_Fv hSig hz v).measurable).add
    (cII_continuous_Fv hSig hz _).measurable))).pow_const p

private theorem cII_Fb_nonneg (A : Matrix (Fin M) (Fin N) ℝ) (v : Fin M ⊕ Fin N → ℝ) (p dv : ℕ)
    {c8 Km K b B : ℝ} (hc8 : 0 ≤ c8) (hKm : 0 ≤ Km) (hK : 0 ≤ K) (hb : 0 ≤ b) (hB : 0 ≤ B) :
    0 ≤ cII_Fb Sig A z v p dv c8 Km K b B := by
  unfold cII_Fb
  refine Finset.sum_nonneg fun μ _ => mul_nonneg ?_ ?_
  · have := cII_w_nonneg N dv (vbar Sig v (Sum.inr μ)); positivity
  · have := cII_a_nonneg (Sig := Sig) (A := A) (z := z) (v := v) (μ := μ) hKm hK hb; positivity

private theorem cII_tagA_zero (A : Matrix (Fin M) (Fin N) ℝ) (v : Fin M ⊕ Fin N → ℝ) (i : Fin M)
    (μ : Fin N) (n : ℕ) (w : Word n) (σ : Fin (n + 1) → Fin 3) (h : tagNZ n w σ = false) :
    tagA Sig A z v i μ n w σ = 0 := by
  cases n with
  | zero => simp [tagNZ] at h
  | succ k =>
    simp only [tagNZ, List.all_eq_false, List.mem_finRange, true_and, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨l, hl⟩ := h
    simp only [tagA]
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    exact brack_eq_zero Sig A z v i μ _ _ _ (by simpa using hl)

end MeasZ

/-! ## The assembly at fixed `N` -/

section Core

variable {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {z : ℂ}

private theorem cII_core {C : ℕ → ℝ} {S : Set ℂ} (hset : CompSetting τ c M N Sig S) (hz : z ∈ S)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X)
    {v : Fin M ⊕ Fin N → ℝ} (hv : testNorm v = 1) {p : ℕ} (hp : 0 < p) (ns : Fin p → ℕ)
    (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3) (cs : Fin p → Bool)
    (hns : ∑ r, ns r = 3) (hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true) (Kt : ℕ)
    {K b b₀ Cn Kmax DA : ℝ} (hK : 1 ≤ K) (hb0 : 0 ≤ b) (hbN : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b)
    (hKb : K * b ≤ b₀) (hBb : K ^ (15 * Kt + 24) * b ≤ b₀) (hb₀1 : b₀ ≤ 1)
    (hε : K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1) ≤ K)
    (hrep : τ⁻¹ * (N : ℝ) ^ 2 * (p + 3) * (K * (K * (N : ℝ) ^ (-τ / 2) * (2 * K)) ^ (Kt + 1)) *
      (2 * K) ^ 12 ≤ 1) (hKmax : 0 ≤ Kmax)
    (Θ : Set Ω) (hΘ : ∀ ω ∈ Θ, ∀ μ, GoodSec8 τ K b Cn Sig (X ω) z v μ)
    (hΘp : HighProbAt N (DA - 4) Θ)
    (hLΘ : ∀ ω ∈ Θ, ∀ (μ : Fin N) (i : Fin M) (k : ℕ) (ct : Fin k → Bool), k ≤ Kt * dMuof σs →
      ‖∫ y, (∏ r, conjIf (cs r) (((tagForms Sig (X ω) z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol (X ω) μ y) z μ)
            ∂(colLaw X μ)‖ ≤
        Kmax * K ^ (dXof ns ws σs + Kt * dMuof σs) *
          (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
              b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0)
            else b ^ dXof ns ws σs))
    (hD : 3 * (((8 * ((3 * Kt + 4) * (p + 3)) + 3 : ℕ)) : ℝ) ≤ DA - 4)
    (hc2 : (τ⁻¹ * (cII_cT Kt p * (2 + cII_KW τ⁻¹ C (2 * ((3 * Kt + 4) * (p + 3)))))) ^ 2 *
        (cII_cU τ c ^ (2 * ((3 * Kt + 4) * (p + 3))) *
          cII_KW τ⁻¹ C (2 * (2 * ((3 * Kt + 4) * (p + 3))))) ≤ N)
    (hτp : τ⁻¹ ^ p ≤ N) (hΨ : τ / N ≤ b₀) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
        ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs * ∏ r, conjIf (cs r)
          (tagA Sig (X ω) z v i μ (ns r) (ws r) (σs r) *
            G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤
      ((2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax + 1) * (1 + 2 * (12 * mBoundConst τ) ^ p) + 2) *
        (b₀ ^ p + maxFp Sig X z v p) := by
  have hF := cII_facts hset hz
  have hN := hF.N1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hKm := hF.Km1
  have hτ := hF.pos
  have hT : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hF.le_one
  obtain ⟨c8, hc8⟩ : ∃ c8 : ℝ, c8 = 2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax := ⟨_, rfl⟩
  rw [← hc8]
  have hc80 : 0 ≤ c8 := by rw [hc8]; have := cII_ck_one Kt; positivity
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = K ^ (15 * Kt + 24) * b := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hbB : b ≤ B := by rw [hBdef]; exact le_mul_of_one_le_left hb0 (one_le_pow₀ hK)
  have hBb' : B ≤ b₀ := by rw [hBdef]; exact hBb
  have hB1 : B ≤ 1 := hBb'.trans hb₀1
  have hb1 : b ≤ 1 := hbB.trans hB1
  have hb₀0 : 0 ≤ b₀ := hb0.trans (hbB.trans hBb')
  set nU := (3 * Kt + 4) * (p + 3) with hnU
  set Km := mBoundConst τ with hKmdef
  have hmaxF := cII_maxFp_nonneg Sig X z v p
  -- the random variables
  let Zf : Matrix (Fin M) (Fin N) ℝ → ℝ := fun A => cII_Z Sig A z v ns ws σs cs Kt
    (fun μ => colLaw X μ)
  let Ff : Matrix (Fin M) (Fin N) ℝ → ℝ := fun A => cII_Fb Sig A z v p (dVof σs) c8 Km K b B
  let ξf : Matrix (Fin M) (Fin N) ℝ → ℝ := fun A => max (Zf A - Ff A) 0
  have hXm := cII_measurable_X hX
  have hZm : Measurable Zf := cII_Z_meas X hF.posDef hF.im_pos v ns ws σs cs Kt
  have hFm : Measurable Ff := cII_Fb_meas hF.posDef hF.im_pos v p _ c8 Km K b B
  have hξm : Measurable ξf := (hZm.sub hFm).max measurable_const
  have hZ0 : ∀ A, 0 ≤ Zf A := fun A => by
    simp only [Zf, cII_Z]
    refine mul_nonneg (Real.rpow_nonneg hNp.le _) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (by positivity))
  have hF0 : ∀ A, 0 ≤ Ff A := fun A => cII_Fb_nonneg A v p _ hc80 (by linarith) hK0 hb0 hB0
  have hξ0 : ∀ A, 0 ≤ ξf A := fun A => le_max_right _ _
  have hξZ : ∀ A, ξf A ≤ Zf A := fun A => max_le (by linarith [hF0 A]) (hZ0 A)
  set cZ := τ⁻¹ * N * (cII_cT Kt p * (2 + cII_KW τ⁻¹ C (2 * nU))) with hcZ
  have hZle : ∀ A, Zf A ≤ cZ * cII_U τ c A ^ nU := fun A =>
    cII_Z_le hX hset hz hv ns ws σs cs hns Kt A
  have hZi : Integrable fun ω => Zf (X ω) :=
    cII_integrable_U hX hF (hZm.comp hXm).aestronglyMeasurable (cf := cZ) (n := nU)
      fun A => by rw [Real.norm_of_nonneg (hZ0 A)]; exact hZle A
  obtain ⟨hFi, hFle⟩ := cII_int_Fb hX hset hz hv p (dVof σs) hc80 hK0 hb0 hB0
  have hξi : Integrable fun ω => ξf (X ω) :=
    hZi.mono' (hξm.comp hXm).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hξ0 _)]; exact hξZ _)
  have hcZ0 : 0 ≤ cZ := by
    rw [hcZ]
    have := cII_cT_one Kt p
    have := cII_KW_nonneg (inv_pos.2 hτ).le C (2 * nU)
    positivity
  have hξ2 : ∀ A, ξf A ^ 2 ≤ cZ ^ 2 * cII_U τ c A ^ (2 * nU) := fun A => by
    calc ξf A ^ 2 ≤ (cZ * cII_U τ c A ^ nU) ^ 2 :=
          pow_le_pow_left₀ (hξ0 A) ((hξZ A).trans (hZle A)) 2
      _ = cZ ^ 2 * cII_U τ c A ^ (2 * nU) := by rw [mul_pow, ← pow_mul, mul_comm nU 2]
  have hξ2i : Integrable fun ω => ξf (X ω) ^ 2 :=
    cII_integrable_U hX hF (f := fun A => ξf A ^ 2)
      ((hξm.pow_const 2).comp hXm).aestronglyMeasurable (cf := cZ ^ 2) (n := 2 * nU) fun A => by
        rw [Real.norm_of_nonneg (pow_nonneg (hξ0 A) 2)]; exact hξ2 A
  -- the second moment
  set Cc : ℕ := 8 * nU + 3 with hCc
  have hξ2le : ∫ ω, ξf (X ω) ^ 2 ≤ (N : ℝ) ^ (Cc : ℝ) := by
    have hUi := cII_integrable_U hX hF (f := fun A => cII_U τ c A ^ (2 * nU))
      (((cII_continuous_sq.const_add 1).pow 2 |>.const_mul _ |>.pow (2 * nU)).measurable.comp
        hXm).aestronglyMeasurable (cf := 1) (n := 2 * nU) fun A => by
          rw [Real.norm_of_nonneg (pow_nonneg (cII_U_nonneg hF A) _), one_mul]
    have hUle := cII_int_U_le hX hF (2 * nU)
    calc ∫ ω, ξf (X ω) ^ 2 ≤ ∫ ω, cZ ^ 2 * cII_U τ c (X ω) ^ (2 * nU) :=
          integral_mono hξ2i (hUi.const_mul _) fun ω => hξ2 (X ω)
      _ = cZ ^ 2 * ∫ ω, cII_U τ c (X ω) ^ (2 * nU) := integral_const_mul _ _
      _ ≤ cZ ^ 2 * (cII_cU τ c ^ (2 * nU) * cII_KW τ⁻¹ C (2 * (2 * nU)) *
            (N : ℝ) ^ (4 * (2 * nU))) := mul_le_mul_of_nonneg_left hUle (by positivity)
      _ = (τ⁻¹ * (cII_cT Kt p * (2 + cII_KW τ⁻¹ C (2 * nU)))) ^ 2 *
            (cII_cU τ c ^ (2 * nU) * cII_KW τ⁻¹ C (2 * (2 * nU))) *
            ((N : ℝ) ^ (2 + 8 * nU)) := by
          rw [hcZ, pow_add]; ring_nf
      _ ≤ (N : ℝ) * (N : ℝ) ^ (2 + 8 * nU) := mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = (N : ℝ) ^ (Cc : ℝ) := by
          rw [Real.rpow_natCast, hCc, ← pow_succ']; ring_nf
  -- the off-`Θ` part
  set Γ := (N : ℝ) ^ (-(Cc : ℝ)) with hΓ
  have hΓ0 : 0 < Γ := Real.rpow_pos_of_pos hNp _
  have hdom : DomAt N 0 (DA - 4) (fun ω => ξf (X ω)) (fun _ => Γ) := by
    unfold DomAt
    refine le_trans (measure_mono fun ω hω => ?_) hΘp
    simp only [Set.mem_ofPred_eq, Real.rpow_zero, one_mul] at hω
    intro hωΘ
    have hZF := cII_onTheta hset hz hv hK hb0 hb1 hbN (hΘ ω hωΘ) hp ns ws σs cs hns hnz Kt
      (by rw [← hBdef]; exact hB1) hKmax hε hrep (fun μ => colLaw X μ)
      (fun μ i k ct => cII_integrable_PG hτ hX hN hF.Mle μ
        (cII_lem87_integrand (X ω) z v i μ ns ws σs cs ct).1
        (cII_lem87_integrand (X ω) z v i μ ns ws σs cs ct).2)
      (hLΘ ω hωΘ)
    have hZF' : Zf (X ω) ≤ Ff (X ω) := by
      simp only [Zf, Ff]; rw [hBdef, hc8]; exact hZF
    have : ξf (X ω) = 0 := max_eq_right (by linarith)
    rw [this] at hω
    linarith
  have hξint := integral_le_of_domAt hN le_rfl hD le_rfl (fun ω => hξ0 (X ω)) hξ2i hξ2le hdom
  rw [Real.rpow_zero, mul_one] at hξint
  -- `N^{−C} ≤ b₀^p`
  have hΓb : Γ ≤ b₀ ^ p := by
    have hNp1 : (0 : ℝ) < (N : ℝ) ^ p := by positivity
    have e1 : Γ = ((N : ℝ) ^ Cc)⁻¹ := by rw [hΓ, Real.rpow_neg hNp.le, Real.rpow_natCast]
    have h1 : (N : ℝ) ^ (p + 1) ≤ (N : ℝ) ^ Cc := pow_le_pow_right₀ hNr (by
      rw [hCc, hnU]; nlinarith)
    have h2 : (τ / N) ^ p ≤ b₀ ^ p := pow_le_pow_left₀ (by positivity) hΨ p
    have h5 : (N : ℝ)⁻¹ ≤ τ ^ p := by
      have := inv_anti₀ (by positivity : (0 : ℝ) < τ⁻¹ ^ p) hτp
      rwa [inv_pow, inv_inv] at this
    have h4 : ((N : ℝ) ^ (p + 1))⁻¹ ≤ (τ / N) ^ p :=
      calc ((N : ℝ) ^ (p + 1))⁻¹ = (N : ℝ)⁻¹ * ((N : ℝ) ^ p)⁻¹ := by
            rw [pow_succ, mul_inv, mul_comm]
        _ ≤ τ ^ p * ((N : ℝ) ^ p)⁻¹ := mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = (τ / N) ^ p := by rw [div_pow, div_eq_mul_inv]
    rw [e1]
    calc ((N : ℝ) ^ Cc)⁻¹ ≤ ((N : ℝ) ^ (p + 1))⁻¹ := inv_anti₀ (by positivity) h1
      _ ≤ _ := h4.trans h2
  -- assembly
  have hLHS := cII_LHS_le hX hset hz hv ns ws σs cs hns Kt
  have hZF : ∫ ω, Zf (X ω) ≤ (∫ ω, Ff (X ω)) + ∫ ω, ξf (X ω) := by
    rw [← integral_add hFi hξi]
    refine integral_mono hZi (hFi.add hξi) fun ω => ?_
    have := le_max_left (Zf (X ω) - Ff (X ω)) 0
    simp only [ξf] at this ⊢
    linarith
  have hBp : B ^ p ≤ b₀ ^ p := pow_le_pow_left₀ hB0 hBb' p
  have hKbp : (K * b) ^ p ≤ b₀ ^ p := pow_le_pow_left₀ (by positivity) hKb p
  have hKm0 : 0 ≤ (12 * Km) ^ p := by positivity
  have hb₀p : 0 ≤ b₀ ^ p := pow_nonneg hb₀0 p
  calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
        ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs * ∏ r, conjIf (cs r)
          (tagA Sig (X ω) z v i μ (ns r) (ws r) (σs r) *
            G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖
      ≤ ∫ ω, Zf (X ω) := hLHS
    _ ≤ (∫ ω, Ff (X ω)) + ∫ ω, ξf (X ω) := hZF
    _ ≤ (c8 + 1) * (B ^ p + (12 * Km) ^ p * ((K * b) ^ p + 2 * maxFp Sig X z v p)) + 2 * Γ :=
        add_le_add hFle hξint
    _ ≤ (c8 + 1) * (b₀ ^ p + (12 * Km) ^ p * (b₀ ^ p + 2 * maxFp Sig X z v p)) + 2 * b₀ ^ p := by
        gcongr
    _ ≤ ((c8 + 1) * (1 + 2 * (12 * Km) ^ p) + 2) * (b₀ ^ p + maxFp Sig X z v p) := by
        have key : 0 ≤ (c8 + 1) * ((12 * Km) ^ p * b₀ ^ p + maxFp Sig X z v p) +
            2 * maxFp Sig X z v p := by positivity
        linarith [key]

end Core

/-! ## The laws of the entries of the column `μ` -/

section EntryLaw

private theorem cII_entryLaw {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    (j : Fin M) (μ : Fin N) :
    IsProbabilityMeasure (entryLaw X (j, μ)) ∧ ∫ y, y ∂(entryLaw X (j, μ)) = 0 ∧
      ∀ n : ℕ, Integrable (fun y => |y| ^ n) (entryLaw X (j, μ)) ∧
        ∫ y, |Real.sqrt N * y| ^ n ∂(entryLaw X (j, μ)) ≤ C n := by
  have hm := hX.measurable j μ
  have hNp : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  unfold entryLaw
  dsimp only
  refine ⟨inferInstance, ?_, fun n => ⟨?_, ?_⟩⟩
  · rw [integral_map (f := fun y : ℝ => y) hm.aemeasurable measurable_id.aestronglyMeasurable]
    exact hX.mean j μ
  · have hc : Measurable fun y : ℝ => |y| ^ n := (continuous_abs.pow n).measurable
    rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
    have e : (fun y : ℝ => |y| ^ n) ∘ (fun ω => X ω j μ) =
        fun ω => ((Real.sqrt N) ^ n)⁻¹ * |Real.sqrt N * X ω j μ| ^ n := by
      funext ω
      simp only [Function.comp, abs_mul, abs_of_pos hNp, mul_pow]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_pos hNp n).ne', one_mul]
    rw [e]
    exact (hX.integrable_moment n j μ).const_mul _
  · have hc : Measurable fun y : ℝ => |Real.sqrt N * y| ^ n :=
      ((continuous_const.mul continuous_id).abs.pow n).measurable
    rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
    exact hX.moment n j μ

end EntryLaw

private theorem cII_DA {τ DA : ℝ} {p : ℕ} (hp2 : 2 ≤ p) (hDA : dPrevTwo τ p ≤ DA) :
    3 * (((8 * ((3 * kTau τ + 4) * (p + 3)) + 3 : ℕ)) : ℝ) ≤ DA - 4 := by
  unfold dPrevTwo dPrev at hDA
  push_cast
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hK : (0 : ℝ) ≤ kTau τ := Nat.cast_nonneg _
  have h1 : 9 * ((p : ℝ) + 3) ≤ 5 * ((p : ℝ) + 1) ^ 2 := by nlinarith
  have h2 : 9 * ((p : ℝ) + 3) * ((kTau τ : ℝ) + 1) ≤ 5 * ((p : ℝ) + 1) ^ 2 * ((kTau τ : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  nlinarith

/-- Lemma 8.8 (`lem:82`), (sec8 2): for tagged words with `∑_r n(w_r) = 3` and any conjugation
pattern, `N^{−3/2} ∑_{i,μ} |E v̄(μ)^{d_v} ∏_r c_r(A(w_r, σ_r) G_μμ^{|σ_r|_μ})| ≤
K((N^{C₀δ}Ψ)^p + max_{𝒱_v} E F^p)`. -/
theorem lem82 (τ c : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : czero τ ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hDA : dPrevTwo τ p ≤ DA) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
      (S : Set ℂ) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C allModels Sig S C₀ δ (m - 1) (δ / 4) DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
          ∀ (ns : Fin p → ℕ) (ws : ∀ r, Word (ns r)) (σs : ∀ r, Fin (ns r + 1) → Fin 3)
            (cs : Fin p → Bool), ∑ r, ns r = 3 →
            (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
              ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs * ∏ r, conjIf (cs r)
                (tagA Sig (X ω) z v i μ (ns r) (ws r) (σs r) *
                  G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤
              K * (((N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z) ^ p + maxFp Sig X z v p) := by
  have _ := hp
  obtain ⟨hC2400, hKt24, hR2, h6δ, h39δ⟩ := cII_params hτ hτ1 hδ hC₀ hC₀δ
  set Kt := kTau τ with hKt
  set Km := mBoundConst τ with hKm
  have hKm1 : 1 ≤ Km := by
    rw [hKm]; unfold mBoundConst genPropConst
    have h2 : (0 : ℝ) < τ / 2 := by positivity
    have h3 : τ / 2 ≤ 1 := by linarith
    rw [le_div_iff₀ (by positivity)]
    have h4 : (τ / 2) ^ 4 ≤ 1 := pow_le_one₀ h2.le h3
    nlinarith
  obtain ⟨Cn, N₁, hΘ⟩ := goodSec8_highProb τ c C C₀ δ DA hτ hτ1 hc hδ hC₀ hC₀δ
  choose Kf hKf0 hKf using fun k => lem87 C τ hτ p k
  set Kmax := ∑ k ∈ Finset.range (Kt * (p + 3) + 1), Kf k with hKmax
  have hKmax0 : 0 ≤ Kmax := Finset.sum_nonneg fun k _ => hKf0 k
  have hKfle : ∀ k ≤ Kt * (p + 3), Kf k ≤ Kmax := fun k hk =>
    Finset.single_le_sum (f := Kf) (fun k _ => hKf0 k) (Finset.mem_range.2 (by omega))
  set nU := (3 * Kt + 4) * (p + 3) with hnU
  set c2 := (τ⁻¹ * (cII_cT Kt p * (2 + cII_KW τ⁻¹ C (2 * nU)))) ^ 2 *
    (cII_cU τ c ^ (2 * nU) * cII_KW τ⁻¹ C (2 * (2 * nU))) with hc2
  have hck := cII_ck_one Kt
  refine ⟨(2 ^ 8 * τ⁻¹ * cII_ck Kt ^ (p + 3) * Kmax + 1) * (1 + 2 * (12 * Km) ^ p) + 2,
    by positivity, ?_⟩
  obtain ⟨N₂, h₂⟩ := cII_eventually0 (Real.sqrt Km) ((C₀ / 2 + 2) * δ) (by positivity)
  obtain ⟨N₃, h₃⟩ := cII_eventually0 (Real.sqrt Km + 1) (τ / 4) (by positivity)
  obtain ⟨N₄, h₄⟩ := cII_eventually0 2 (τ / 4) (by positivity)
  obtain ⟨N₅, h₅⟩ := cII_eventually0 (τ⁻¹ * (p + 3) * 2 ^ 12 * 2 ^ (Kt + 1)) 1 one_pos
  obtain ⟨N₆, h₆⟩ := cII_eventually0 c2 1 one_pos
  obtain ⟨N₇, h₇⟩ := cII_eventually0 (τ⁻¹ ^ p) 1 one_pos
  refine ⟨max (max N₁ (max N₂ N₃)) (max (max N₄ N₅) (max N₆ (max N₇ 1))), ?_⟩
  intro N hN M Sig S m hset hm hPA Ω _ _ X hX z hz v hv ns ws σs cs hns
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN₁, hN₂, hN₃⟩, ⟨hN₄, hN₅⟩, hN₆, hN₇, hN1⟩ := hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hzS : z ∈ S := hz.1
  have hF := cII_facts hset hzS
  obtain ⟨hΨlow, hΨup, hΨτ⟩ := cII_Psi_bounds hset hzS
  set Ψ := Psi N (specOf Sig) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨτ
  have hmaxF := cII_maxFp_nonneg Sig X z v p
  -- the vanishing tagged words
  by_cases hnz : ∀ r, tagNZ (ns r) (ws r) (σs r) = true
  swap
  · obtain ⟨r₀, hr₀⟩ := not_forall.1 hnz
    have hzero : ∀ (i : Fin M) (μ : Fin N) (ω : Ω), ∏ r, conjIf (cs r)
        (tagA Sig (X ω) z v i μ (ns r) (ws r) (σs r) *
          G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r)) = 0 := by
      intro i μ ω
      refine Finset.prod_eq_zero (Finset.mem_univ r₀) ?_
      rw [cII_tagA_zero (X ω) v i μ _ _ _ (by simpa using hr₀), zero_mul]
      cases cs r₀ <;> simp [conjIf]
    simp only [hzero, mul_zero, integral_zero, norm_zero, Finset.sum_const_zero]
    positivity
  -- the levels
  set K := (N : ℝ) ^ (3 * δ) with hKdef
  set b := (N : ℝ) ^ ((C₀ / 2 + 2) * δ) * Ψ with hbdef
  set b₀ := (N : ℝ) ^ (C₀ * δ) * Ψ with hb₀def
  have hK : 1 ≤ K := Real.one_le_rpow hNr (by positivity)
  have hb0 : 0 ≤ b := by positivity
  have hrp : ∀ a a' : ℝ, a ≤ a' → (N : ℝ) ^ a * Ψ ≤ (N : ℝ) ^ a' * Ψ := fun a a' h =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hNr h) hΨ0
  have hbN : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ b := by
    rw [cII_rpow_half]
    calc (Real.sqrt N)⁻¹ ≤ Real.sqrt Km * Ψ := hΨlow
      _ ≤ (N : ℝ) ^ ((C₀ / 2 + 2) * δ) * Ψ := mul_le_mul_of_nonneg_right (h₂ N hN₂) hΨ0
  have hKb : K * b ≤ b₀ := by
    rw [hKdef, hbdef, hb₀def, ← mul_assoc, ← Real.rpow_add hNp]
    exact hrp _ _ (by nlinarith)
  have hBb : K ^ (15 * Kt + 24) * b ≤ b₀ := by
    rw [hKdef, hbdef, hb₀def, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← mul_assoc,
      ← Real.rpow_add hNp]
    refine hrp _ _ ?_
    push_cast
    nlinarith
  have hb₀1 : b₀ ≤ 1 := by
    have h1 : (N : ℝ) ^ (C₀ * δ) ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hNr hC₀δ
    have h2 := h₃ N hN₃
    have h3 : (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (-(τ / 2)) = ((N : ℝ) ^ (τ / 4))⁻¹ := by
      rw [← Real.rpow_add hNp, ← Real.rpow_neg hNp.le]; ring_nf
    have hq0 : 0 < (N : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hNp _
    calc b₀ = (N : ℝ) ^ (C₀ * δ) * Ψ := rfl
      _ ≤ (N : ℝ) ^ (τ / 4) * ((Real.sqrt Km + 1) * (N : ℝ) ^ (-(τ / 2))) :=
          mul_le_mul h1 hΨup hΨ0 hq0.le
      _ = (Real.sqrt Km + 1) * ((N : ℝ) ^ (τ / 4))⁻¹ := by rw [← h3]; ring
      _ ≤ (N : ℝ) ^ (τ / 4) * ((N : ℝ) ^ (τ / 4))⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hb1 : b ≤ 1 := by
    have : b ≤ b₀ := hrp _ _ (by nlinarith)
    linarith
  obtain ⟨hε, hrep⟩ := cII_rep_num (Kt := Kt) (p := p) hNr hτ hδ hKt24 h6δ h39δ (h₄ N hN₄)
    (by have := h₅ N hN₅; rwa [Real.rpow_one] at this)
  -- the event `Θ` and Lemma 8.11 on it
  have hΘp := hΘ N hN₁ M Sig S allModels m hset hm hPA Ω X hX trivial z hz v hv
  have hLΘ : ∀ ω ∈ {ω | ∀ μ, GoodSec8 τ ((N : ℝ) ^ (3 * δ))
      ((N : ℝ) ^ ((C₀ / 2 + 2) * δ) * Psi N (specOf Sig) z) Cn Sig (X ω) z v μ},
      ∀ (μ : Fin N) (i : Fin M) (k : ℕ) (ct : Fin k → Bool), k ≤ Kt * dMuof σs →
      ‖∫ y, (∏ r, conjIf (cs r) (((tagForms Sig (X ω) z v i μ (ns r) (ws r) (σs r)).map
          fun c => linForm c y).prod)) * ∏ t, conjIf (ct t) (Qmu Sig (updCol (X ω) μ y) z μ)
            ∂(colLaw X μ)‖ ≤
        Kmax * K ^ (dXof ns ws σs + Kt * dMuof σs) *
          (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
              b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0)
            else b ^ dXof ns ws σs) := by
    intro ω hω μ i k ct hk
    have hρ : ∀ j, IsProbabilityMeasure (entryLaw X (j, μ)) := fun j =>
      (cII_entryLaw hX hN1 j μ).1
    have h87 := hKf k M N Sig (X ω) z v i μ (fun j => entryLaw X (j, μ)) K b hN1 hF.Mle hK hbN
      hb1 (fun j => (cII_entryLaw hX hN1 j μ).2.1) (fun j n => (cII_entryLaw hX hN1 j μ).2.2 n)
      (hω μ).toGoodMinor ns ws σs cs ct hns hnz
    have hβ0 : 0 ≤ (if dVof σs = 0 then (N : ℝ) ^ (-(1 : ℝ) / 2) *
        b ^ (dXof ns ws σs - if 3 ≤ dXof ns ws σs then 1 else 0) else b ^ dXof ns ws σs) := by
      split_ifs <;> first
        | exact pow_nonneg hb0 _
        | exact mul_nonneg (Real.rpow_nonneg hNp.le _) (pow_nonneg hb0 _)
    have hk' : k ≤ Kt * (p + 3) := hk.trans (Nat.mul_le_mul_left _ (cII_dMu_le ns σs hns))
    refine h87.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul (hKfle k hk')
      (pow_le_pow_right₀ hK (by omega)) (by positivity) hKmax0) hβ0
  have hD := cII_DA hp2 hDA
  exact cII_core hset hzS hX hv (by omega) ns ws σs cs hns hnz Kt hK hb0 hbN hKb hBb hb₀1 hε hrep
    hKmax0 _ (fun ω hω => hω) hΘp hLΘ hD (by have := h₆ N hN₆; rwa [Real.rpow_one] at this)
    (by have := h₇ N hN₇; rwa [Real.rpow_one] at this)
    (hΨτ.trans (le_mul_of_one_le_left hΨ0 (Real.one_le_rpow hNr (by positivity))))

/-! ### Instances -/

section Checks

open Complex

/-- Lemma 8.8 at `τ = 1/2`, `c = 1`, `C_p = 2`, `p = 2`, `C₀ = C₀(1/2) = 4800`,
`δ = min(1, 1/2)/(4 C₀(1/2)) = 1/38400`, `D_A = D(1/2, 2)` and the word lengths `n = (3, 0)`
(one word with three pairs and one empty word): the parameter hypotheses are discharged and the
model hypotheses stay binders of the conclusion. At `N = 2` the level `N^{C₀δ} Ψ` exceeds `1`, so
the bound is meaningful only for large `N`. -/
example : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ)
    (S : Set ℂ) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
    PropA N (fun _ => 2) allModels Sig S (czero (1 / 2)) (deltaTwo 1 (1 / 2)) (m - 1)
      (deltaTwo 1 (1 / 2) / 4) (dPrevTwo (1 / 2) 2) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X →
      ∀ z ∈ levelSet N (deltaTwo 1 (1 / 2)) S m, ∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 →
        ∀ (ws : ∀ r, Word ((![3, 0] : Fin 2 → ℕ) r))
          (σs : ∀ r, Fin ((![3, 0] : Fin 2 → ℕ) r + 1) → Fin 3) (cs : Fin 2 → Bool),
          (N : ℝ) ^ (-(3 : ℝ) / 2) * ∑ i, ∑ μ,
            ‖∫ ω, ((vbar Sig v (Sum.inr μ) : ℝ) : ℂ) ^ dVof σs * ∏ r, conjIf (cs r)
              (tagA Sig (X ω) z v i μ ((![3, 0] : Fin 2 → ℕ) r) (ws r) (σs r) *
                G Sig (X ω) z (Sum.inr μ) (Sum.inr μ) ^ tagMu (σs r))‖ ≤
            K * (((N : ℝ) ^ (czero (1 / 2) * deltaTwo 1 (1 / 2)) * Psi N (specOf Sig) z) ^ 2 +
              maxFp Sig X z v 2) := by
  have hc : czero (1 / 2) = 4800 := by norm_num [czero]
  have hd : deltaTwo 1 (1 / 2) = 1 / 38400 := by
    rw [deltaTwo, hc]; norm_num
  obtain ⟨K, hK, N₀, h⟩ := lem82 (1 / 2) 1 (fun _ => 2) 2 (czero (1 / 2)) (deltaTwo 1 (1 / 2))
    (dPrevTwo (1 / 2) 2) (by norm_num) (by norm_num) one_pos even_two le_rfl
    (by rw [hd]; norm_num) le_rfl (by rw [hc, hd]; norm_num) le_rfl
  exact ⟨K, hK, N₀, fun N hN M Sig S m h1 h2 h3 Ω _ _ X hX z hz v hv ws σs cs =>
    h N hN M Sig S m h1 h2 h3 Ω X hX z hz v hv _ ws σs cs (by simp)⟩

/-- The unit vector `e_{inl 0}` of `𝓘 = Fin 2 ⊕ Fin 2`. -/
local notation "e₀" => (eI (Sum.inl (0 : Fin 2)) : Fin 2 ⊕ Fin 2 → ℝ)

/-- `Σ = I` at `M = 2`. -/
local notation "Σ₂" => (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- `X = 0` at `M = N = 2`. -/
local notation "X₂" => (0 : Matrix (Fin 2) (Fin 2) ℝ)

/-- `𝒱_v` at `M = N = 2`: `𝒱_{e_μ} ⊆ 𝒱_v` through `vfam_closed`, with the members `v` and
`e_{μ}` of `𝒱_v` for `v = e_{inl 0}`. -/
example : vfam e₀ none = eI (Sum.inl 0) ∧ vfam e₀ (some 1) = eI (Sum.inr 1) ∧
    ∃ u' : Option (Fin 2), vfam (vfam e₀ (some 1)) none = vfam e₀ u' :=
  ⟨rfl, rfl, vfam_closed e₀ (some 1) none⟩

/-- `max_{𝒱_v} E F^2` at `M = N = 2`, `Σ = I`, `X = 0`, `z = i` on any probability space: the
maximum over the three members `v`, `e_0`, `e_1` of `𝒱_v` of `F_w(0)^2`, and it dominates
`F_v(0)^2` and `F_{e_1}(0)^2`. -/
example (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (v : Fin 2 ⊕ Fin 2 → ℝ) :
    maxFp Σ₂ (fun _ : Ω => X₂) I v 2 = ⨆ w : Option (Fin 2), Fv Σ₂ X₂ I (vfam v w) ^ 2 ∧
      Fv Σ₂ X₂ I v ^ 2 ≤ maxFp Σ₂ (fun _ : Ω => X₂) I v 2 ∧
      Fv Σ₂ X₂ I (eI (Sum.inr 1)) ^ 2 ≤ maxFp Σ₂ (fun _ : Ω => X₂) I v 2 := by
  have e : maxFp Σ₂ (fun _ : Ω => X₂) I v 2 = ⨆ w : Option (Fin 2), Fv Σ₂ X₂ I (vfam v w) ^ 2 := by
    simp [maxFp, integral_const]
  have hb := Finite.bddAbove_range (fun w : Option (Fin 2) => Fv Σ₂ X₂ I (vfam v w) ^ 2)
  refine ⟨e, ?_, ?_⟩
  · rw [e]; exact le_ciSup hb none
  · rw [e]; exact le_ciSup hb (some 1)

end Checks

end Anisotropic
