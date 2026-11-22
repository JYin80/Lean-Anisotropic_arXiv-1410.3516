module

public import Anisotropic.Comparison.Props
public import Anisotropic.LinAlg.Spectral
public import Anisotropic.Density.Varrho
public import Anisotropic.Framework.DominationUnion
public import Anisotropic.Probability.NormBound.Main

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Lemma 7.12 (rough bound), Stieltjes monotonicities, Lemma 7.13 (a priori bounds) -/

/-! ## The Poisson kernel `y / (t² + y²)` -/

/-- The kernel `y / (t² + y²) = Im (t − iy)⁻¹`. -/
private def rbKer (t y : ℝ) : ℝ := y / (t ^ 2 + y ^ 2)

private theorem rbKer_nonneg (t : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ rbKer t y :=
  div_nonneg hy (by positivity)

/-- `y ↦ y · y / (t² + y²)` is nondecreasing on `(0, ∞)`. -/
private theorem rbKer_mul_mono (t : ℝ) {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h : y₁ ≤ y₂) :
    y₁ * rbKer t y₁ ≤ y₂ * rbKer t y₂ := by
  have h₂ : 0 < y₂ := h₁.trans_le h
  unfold rbKer
  rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hyy : y₁ * y₁ ≤ y₂ * y₂ := mul_le_mul h h h₁.le h₂.le
  nlinarith [mul_le_mul_of_nonneg_right hyy (sq_nonneg t)]

/-- `y ↦ y⁻¹ · y / (t² + y²)` is nonincreasing on `(0, ∞)`. -/
private theorem rbKer_div_anti (t : ℝ) {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h : y₁ ≤ y₂) :
    rbKer t y₂ / y₂ ≤ rbKer t y₁ / y₁ := by
  have h₂ : 0 < y₂ := h₁.trans_le h
  have e : ∀ y : ℝ, 0 < y → rbKer t y / y = 1 / (t ^ 2 + y ^ 2) := by
    intro y hy
    unfold rbKer
    field_simp
  rw [e y₁ h₁, e y₂ h₂]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- `k(t, a) ≤ (b / a) k(t, b)` for `0 < a ≤ b`. -/
private theorem rbKer_le_ratio (t : ℝ) {a b : ℝ} (ha : 0 < a) (h : a ≤ b) :
    rbKer t a ≤ b / a * rbKer t b := by
  have := rbKer_mul_mono t ha h
  rw [div_mul_eq_mul_div, le_div_iff₀ ha]
  linarith

/-- `Im (x − z)⁻¹ = k(x − Re z, Im z)`. -/
private theorem rb_inv_im (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).im = rbKer (x - z.re) z.im := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  unfold rbKer
  ring

/-- `|(x − z)⁻¹| = ((x − Re z)² + (Im z)²)^{−1/2}`. -/
private theorem rb_inv_norm (x : ℝ) (z : ℂ) :
    ‖((x : ℂ) - z)⁻¹‖ = (√((x - z.re) ^ 2 + z.im ^ 2))⁻¹ := by
  rw [norm_inv, Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
    neg_sq]

/-! ## The dyadic windows of Lemma 7.12 -/

/-- `|t|⁻¹ ≤ 2 b / (t² + a²)` when `0 < a ≤ |t| < b`. -/
private theorem rb_window (t : ℝ) {a b : ℝ} (ha : 0 < a) (hat : a ≤ |t|) (htb : |t| < b) :
    |t|⁻¹ ≤ 2 * (b / a) * rbKer t a := by
  have ht : 0 < |t| := ha.trans_le hat
  have e : 2 * (b / a) * rbKer t a = 2 * b / (t ^ 2 + a ^ 2) := by
    unfold rbKer
    field_simp
  rw [e, inv_eq_one_div, div_le_div_iff₀ ht (by positivity)]
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  nlinarith [mul_le_mul hat hat ha.le ht.le]

/-- One eigenvalue in Lemma 7.12 for `Im z < 1`: `|λ − z|⁻¹` is bounded by the ladder sum. -/
private theorem rb_ladder_term {N : ℕ} (hN : 1 < N) {δ η t T : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hη1 : η < 1) (htT : |t| ≤ T) :
    (√(t ^ 2 + η ^ 2))⁻¹ ≤ (6 * (N : ℝ) ^ (2 * δ) + 2 * T) *
      ∑ l ∈ Finset.Icc 1 (ladderL N δ η), rbKer t (ladderEta N δ η l) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNδ : 1 < (N : ℝ) ^ δ := Real.one_lt_rpow hN1 hδ
  have hηN : η < (N : ℝ) ^ δ := hη1.trans hNδ
  have hN2 : (N : ℝ) ^ (2 * δ) = (N : ℝ) ^ δ * (N : ℝ) ^ δ := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  set L := ladderL N δ η with hLdef
  set e : ℕ → ℝ := ladderEta N δ η with hedef
  have hL : 1 ≤ L := by
    rw [hLdef, ladderL, Nat.one_le_iff_ne_zero, ne_eq, Nat.ceil_eq_zero, not_le]
    exact div_pos (Real.log_pos (one_lt_inv₀ hη |>.2 hη1))
      (mul_pos hδ (Real.log_pos hN1))
  have he0 : e 0 = η := by
    have h0 : 0 < ladderL N δ η := by omega
    simp [hedef, ladderEta, h0]
  have heL : e L = 1 := by
    simp [hedef, ladderEta, hLdef]
  have hb := fun l => ladderEta_bounds hN hδ hη hη1.le l
  have hpos : ∀ l, 0 < e l := fun l => hη.trans_le (hb l).1
  have hsucc : ∀ l, l < L → e (l + 1) ≤ (N : ℝ) ^ δ * e l :=
    fun l hl => ladderEta_succ_le hN hδ hη hηN hl
  have hT : 0 ≤ T := (abs_nonneg t).trans htT
  set C := 6 * (N : ℝ) ^ (2 * δ) + 2 * T with hC
  have hNδ2 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (2 * δ) := by rw [hN2]; nlinarith
  have hker : ∀ l, 0 ≤ rbKer t (e l) := fun l => rbKer_nonneg t (hpos l).le
  -- one window suffices
  suffices hj : ∃ j ∈ Finset.Icc 1 L, (√(t ^ 2 + η ^ 2))⁻¹ ≤ C * rbKer t (e j) by
    obtain ⟨j, hj, hle⟩ := hj
    exact hle.trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun l _ => hker l) hj) (by positivity))
  have hr : 0 < √(t ^ 2 + η ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hrt : |t| ≤ √(t ^ 2 + η ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hrη : η ≤ √(t ^ 2 + η ^ 2) :=
    calc η = √(η ^ 2) := (Real.sqrt_sq hη.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  -- the first window bound `k(t, η) ≤ N^δ k(t, η₁)`
  have h01 : rbKer t η ≤ (N : ℝ) ^ δ * rbKer t (e 1) := by
    have h1 := hsucc 0 (by omega)
    rw [he0] at h1
    have hr1 := rbKer_le_ratio t hη (he0 ▸ (hb 0).2.2 : η ≤ e 1)
    refine hr1.trans (mul_le_mul_of_nonneg_right ?_ (hker 1))
    rw [div_le_iff₀ hη]; exact h1
  rcases lt_or_ge |t| η with hA | hA
  · -- `|λ − E| < η`
    refine ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hL⟩, ?_⟩
    have h1 : (√(t ^ 2 + η ^ 2))⁻¹ ≤ 2 * rbKer t η := by
      unfold rbKer
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hr (by positivity)]
      have : t ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      nlinarith
    calc _ ≤ 2 * rbKer t η := h1
      _ ≤ 2 * ((N : ℝ) ^ δ * rbKer t (e 1)) := by linarith
      _ ≤ C * rbKer t (e 1) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by rw [hC]; nlinarith) (hker 1)
  have hinv : (√(t ^ 2 + η ^ 2))⁻¹ ≤ |t|⁻¹ :=
    inv_anti₀ (hη.trans_le hA) hrt
  rcases lt_or_ge |t| 1 with hB | hB
  · -- `η ≤ |λ − E| < 1`: the window `η_{l−1} ≤ |λ − E| < η_l`
    have hex : ∃ l, |t| < e l := ⟨L, by rw [heL]; exact hB⟩
    set l₀ := Nat.find hex with hl₀
    have hl₀t : |t| < e l₀ := Nat.find_spec hex
    have hl₀L : l₀ ≤ L := Nat.find_min' hex (by rw [heL]; exact hB)
    have hl₀0 : l₀ ≠ 0 := by
      intro h0
      rw [h0, he0] at hl₀t
      linarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl₀0
    have hkt : e k ≤ |t| := by
      have := Nat.find_min hex (show k < l₀ by omega)
      exact not_lt.1 this
    have hw := rb_window t (hpos k) hkt (hk ▸ hl₀t)
    have hratio : e (k + 1) / e k ≤ (N : ℝ) ^ δ := by
      rw [div_le_iff₀ (hpos k)]; exact hsucc k (by omega)
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      refine ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hL⟩, ?_⟩
      rw [he0] at hw hratio
      calc _ ≤ |t|⁻¹ := hinv
        _ ≤ 2 * (e (0 + 1) / η) * rbKer t η := hw
        _ ≤ 2 * (N : ℝ) ^ δ * ((N : ℝ) ^ δ * rbKer t (e 1)) := by
            refine mul_le_mul (by linarith) h01 (rbKer_nonneg t hη.le) (by positivity)
        _ ≤ C * rbKer t (e 1) := by
            rw [← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (hker 1)
            rw [hC, mul_assoc, ← hN2]; nlinarith
    · refine ⟨k, Finset.mem_Icc.2 ⟨hk0, by omega⟩, ?_⟩
      calc _ ≤ |t|⁻¹ := hinv
        _ ≤ 2 * (e (k + 1) / e k) * rbKer t (e k) := hw
        _ ≤ C * rbKer t (e k) := by
            refine mul_le_mul_of_nonneg_right ?_ (hker k)
            rw [hC]; nlinarith
  · -- `|λ − E| ≥ 1 = η_L`
    refine ⟨L, Finset.mem_Icc.2 ⟨hL, le_rfl⟩, ?_⟩
    have ht : 0 < |t| := one_pos.trans_le hB
    have h2 : |t|⁻¹ ≤ 2 * |t| * rbKer t 1 := by
      unfold rbKer
      rw [inv_eq_one_div, mul_div_assoc', mul_one, div_le_div_iff₀ ht (by positivity)]
      have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      nlinarith
    calc _ ≤ |t|⁻¹ := hinv
      _ ≤ 2 * |t| * rbKer t 1 := h2
      _ ≤ C * rbKer t (e L) := by
          rw [heL]
          refine mul_le_mul_of_nonneg_right ?_ (rbKer_nonneg t zero_le_one)
          rw [hC]; nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ N by linarith) (2 * δ)]

/-- One eigenvalue for `Im z ≥ 1`: `|λ − z|⁻¹ ≤ (1 + T) k(λ − E, η)` when `|λ − E| ≤ T`. -/
private theorem rb_top_term {η t T : ℝ} (hη : 1 ≤ η) (htT : |t| ≤ T) :
    (√(t ^ 2 + η ^ 2))⁻¹ ≤ (1 + T) * rbKer t η := by
  have hη0 : 0 < η := one_pos.trans_le hη
  have hT : 0 ≤ T := (abs_nonneg t).trans htT
  have hsq : t ^ 2 + η ^ 2 = √(t ^ 2 + η ^ 2) * √(t ^ 2 + η ^ 2) :=
    (Real.mul_self_sqrt (by positivity)).symm
  set r := √(t ^ 2 + η ^ 2) with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hrle : r ≤ |t| + η := by
    rw [hrdef, Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs t, abs_nonneg t]
  unfold rbKer
  rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hr (by positivity), hsq]
  have : r ≤ (1 + T) * η := by nlinarith [mul_le_mul_of_nonneg_left hη hT]
  nlinarith

/-! ## The spectral form of `G` (decompfullG) -/

/-- The eigenvalues `λ_k` of `Aᵀ Σ A`. -/
private def rbEig {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (k : Fin N) : ℝ :=
  (XSX_isHermitian hSig.1 A).eigenvalues k

/-- The vectors `u_k = Σ̲ J ζ_k` of (decompfullG). -/
private def rbU {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (k : Fin N) : Fin M ⊕ Fin N → ℝ :=
  SigU (n := Fin N) Sig *ᵥ Jmat A *ᵥ ((XSX_isHermitian hSig.1 A).eigenvectorBasis k).ofLp

private theorem rb_ent_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A + B) v w = ent A v w + ent B v w := by
  simp [ent, add_mulVec, dotProduct_add]

private theorem rb_ent_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (A - B) v w = ent A v w - ent B v w := by
  simp [ent, sub_mulVec, dotProduct_sub]

private theorem rb_ent_neg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v w : ι → ℝ) :
    ent (-A) v w = -ent A v w := by
  simp [ent, neg_mulVec, dotProduct_neg]

private theorem rb_ent_cplx {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ) :
    ent (cplx A) v w = ((v ⬝ᵥ A *ᵥ w : ℝ) : ℂ) := by
  simp [ent, cplx, dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

private theorem rb_ent_spec {ι κ : Type*} [Fintype ι] (s : Finset κ) (c : κ → ℂ)
    (u : κ → ι → ℝ) (v w : ι → ℝ) :
    ent (∑ k ∈ s, c k • vecMulVec (cvec (u k)) (cvec (u k))) v w =
      ∑ k ∈ s, (((v ⬝ᵥ u k) * (w ⬝ᵥ u k) : ℝ) : ℂ) * c k := by
  simp only [ent, sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul, dotProduct, cvec, Complex.ofReal_mul, Complex.ofReal_sum]
  have e : ∑ x, ((u k x : ℝ) : ℂ) * ((w x : ℝ) : ℂ) = ∑ x, ((w x : ℝ) : ℂ) * ((u k x : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e]
  ring

/-- (decompfullG) tested at real `x, y`. -/
private theorem rb_ent_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (G Sig A z) x y = -((x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y : ℝ) : ℂ)
      + ∑ k, (((x ⬝ᵥ rbU hSig A k) * (y ⬝ᵥ rbU hSig A k) : ℝ) : ℂ) *
        ((rbEig hSig A k : ℂ) - z)⁻¹ := by
  rw [decompfullG_spec hSig A hz, rb_ent_add, rb_ent_neg, rb_ent_cplx, rb_ent_spec]
  rfl

/-- `Im G_{xx}(z) = ∑_k ⟨x, u_k⟩² Im (λ_k − z)⁻¹`. -/
private theorem rb_im {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x : Fin M ⊕ Fin N → ℝ) :
    (ent (G Sig A z) x x).im =
      ∑ k, (x ⬝ᵥ rbU hSig A k) ^ 2 * rbKer (rbEig hSig A k - z.re) z.im := by
  rw [rb_ent_G hSig A hz, Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add,
    Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.im_ofReal_mul, rb_inv_im, sq]

private theorem rb_im_nonneg {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (x : Fin M ⊕ Fin N → ℝ) :
    0 ≤ (ent (G Sig A z) x x).im := by
  rw [rb_im hSig A hz]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (rbKer_nonneg _ hz.le)


/-! ## Eigenvalue bounds -/

/-- `Σ = U diag(σ) Uᵀ` with `U` orthogonal and `σ = specOf Σ > 0`. -/
private theorem rb_diag {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) :
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

/-- `|Uᵀ x| = |x|` for orthogonal `U`. -/
private theorem rb_sum_sq_UT {K : ℕ} {U : Matrix (Fin K) (Fin K) ℝ} (h₂ : U * Uᵀ = 1)
    (x : Fin K → ℝ) : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have e : (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, h₂, one_mulVec, dotProduct_comm]
  simpa [dotProduct, sq] using e

/-- `⟨w, Σ w⟩ ≤ τ⁻¹ |w|²` under (bound_Sigma). -/
private theorem rb_quad_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : SigmaAssumption τ Sig)
    (w : Fin M → ℝ) : w ⬝ᵥ Sig *ᵥ w ≤ τ⁻¹ * (w ⬝ᵥ w) := by
  obtain ⟨U, h₂, -, hSd, -⟩ := rb_diag hS.posDef
  have hle : ∀ i, specOf Sig i ≤ τ⁻¹ := fun i => by
    rw [specOf_eq hS.posDef.isHermitian]; exact hS.eigenvalues_le i
  have e : w ⬝ᵥ Sig *ᵥ w = ∑ i, specOf Sig i * (Uᵀ *ᵥ w) i ^ 2 := by
    conv_lhs => rw [hSd]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : w ⬝ᵥ w = ∑ i, w i ^ 2 := by simp [dotProduct, sq]
  rw [e, e2, ← rb_sum_sq_UT h₂ w, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)

/-- `|A ζ|² ≤ ‖AᵀA‖` for a unit vector `ζ`. -/
private theorem rb_normsq_le (A : Matrix (Fin M) (Fin N) ℝ) (ζ : EuclideanSpace ℝ (Fin N))
    (hζ : ‖ζ‖ = 1) : (A *ᵥ ζ.ofLp) ⬝ᵥ (A *ᵥ ζ.ofLp) ≤ ‖Aᵀ * A‖ := by
  have h := l2_opNorm_mulVec A ζ
  rw [hζ, mul_one] at h
  have hAA : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact l2_opNorm_conjTranspose_mul_self A
  have e : (A *ᵥ ζ.ofLp) ⬝ᵥ (A *ᵥ ζ.ofLp) =
      ‖(EuclideanSpace.equiv (Fin M) ℝ).symm (A *ᵥ ζ.ofLp)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  rw [e, hAA, sq]
  exact mul_le_mul h h (norm_nonneg _) (norm_nonneg _)

private theorem rbEig_nonneg {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (k : Fin N) : 0 ≤ rbEig hSig A k := by
  have h : (Aᵀ * Sig * A).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hSig.posSemidef.conjTranspose_mul_mul_same A
  exact h.eigenvalues_nonneg k

/-- `λ_k ≤ ‖Σ‖ ‖AᵀA‖ ≤ τ⁻¹ ‖AᵀA‖`. -/
private theorem rbEig_le {τ : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} (hS : SigmaAssumption τ Sig)
    (hτ : 0 < τ) (A : Matrix (Fin M) (Fin N) ℝ) (k : Fin N) :
    rbEig hS.posDef A k ≤ τ⁻¹ * ‖Aᵀ * A‖ := by
  set hH := XSX_isHermitian hS.posDef.1 A
  set ζ := hH.eigenvectorBasis k
  have e1 : rbEig hS.posDef A k = ζ.ofLp ⬝ᵥ (Aᵀ * Sig * A) *ᵥ ζ.ofLp := by
    rw [rbEig, hH.eigenvalues_eq]
    simp [ζ]
  have e2 : ζ.ofLp ⬝ᵥ (Aᵀ * Sig * A) *ᵥ ζ.ofLp =
      (A *ᵥ ζ.ofLp) ⬝ᵥ Sig *ᵥ (A *ᵥ ζ.ofLp) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [e1, e2]
  refine (rb_quad_le hS _).trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hτ.le))
  exact rb_normsq_le A ζ (hH.eigenvectorBasis.orthonormal.1 k)

/-! ## The `Π` part of `G − Π` -/

/-- `(1 + w Σ)⁻¹ = U diag((1 + σᵢ w)⁻¹) Uᵀ` when every `1 + σᵢ w ≠ 0`. -/
private theorem rb_cinv_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    (1 + w • cplx Sig)⁻¹ =
      (cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ := by
  have c₂ : (cplx Uᵀ)ᵀ * cplx Uᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₂,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hT : 1 + w • cplx Sig =
      (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ := by
    have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
      simp only [cplx]
      rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
        diagonal_map (map_zero _)]
      rfl
    have e2 : diagonal (fun i => 1 + (σ i : ℂ) * w) =
        1 + w • diagonal (fun i => (σ i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_smul, diagonal_add]
      congr 1
      funext i
      simp [mul_comm]
    rw [e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, c₂, Matrix.mul_smul,
      Matrix.smul_mul, e1]
  apply Matrix.inv_eq_right_inv
  rw [hT]
  have hd : diagonal (fun i => 1 + (σ i : ℂ) * w) *
      diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hw i)
  calc (cplx Uᵀ)ᵀ * diagonal (fun i => 1 + (σ i : ℂ) * w) * cplx Uᵀ *
        ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ)
      = (cplx Uᵀ)ᵀ * (diagonal (fun i => 1 + (σ i : ℂ) * w) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
          diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [c₁, Matrix.mul_one, hd, Matrix.mul_one, c₂]

/-- The block `−Σ(1 + wΣ)⁻¹` of `Π` in the eigenbasis of `Σ`. -/
private theorem rb_piBlock_eq {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) :
    -(cplx Sig * (1 + w • cplx Sig)⁻¹) =
      (cplx Uᵀ)ᵀ * diagonal (fun i => -((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ := by
  have c₁ : cplx Uᵀ * (cplx Uᵀ)ᵀ = 1 := by
    simp only [cplx]
    rw [← transpose_map, transpose_transpose, ← Matrix.map_mul, h₁,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : cplx Sig = (cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ := by
    simp only [cplx]
    rw [hS, ← transpose_map, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
      diagonal_map (map_zero _)]
    rfl
  rw [rb_cinv_eq h₂ h₁ hS hw, e1]
  calc -((cplx Uᵀ)ᵀ * diagonal (fun i => (σ i : ℂ)) * cplx Uᵀ *
        ((cplx Uᵀ)ᵀ * diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹) * cplx Uᵀ))
      = -((cplx Uᵀ)ᵀ * (diagonal (fun i => (σ i : ℂ)) * (cplx Uᵀ * (cplx Uᵀ)ᵀ) *
          diagonal (fun i => (1 + (σ i : ℂ) * w)⁻¹)) * cplx Uᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [c₁, Matrix.mul_one, diagonal_mul_diagonal, ← Matrix.neg_mul, ← Matrix.mul_neg,
          ← diagonal_neg]

/-- `⟨a, diag(P, Q) b⟩ = ⟨a_M, P b_M⟩ + ⟨a_N, Q b_N⟩`. -/
private theorem rb_ent_blocks (P : Matrix (Fin M) (Fin M) ℂ) (Q : Matrix (Fin N) (Fin N) ℂ)
    (a b : Fin M ⊕ Fin N → ℝ) :
    ent (fromBlocks P 0 0 Q) a b = ent P (a ∘ Sum.inl) (b ∘ Sum.inl) +
      ent Q (a ∘ Sum.inr) (b ∘ Sum.inr) := by
  simp only [ent, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, zero_mulVec, add_zero, zero_add]
  rfl

/-- `Π_{xy} = ∑ᵢ pᵢ qᵢ (−σᵢ/(1 + σᵢ w)) + w ⟨x_N, y_N⟩` with `p = Uᵀ x_M`, `q = Uᵀ y_M`. -/
private theorem rb_pi_coord {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ) {w : ℂ}
    (hw : ∀ i, 1 + (σ i : ℂ) * w ≠ 0) (x y : Fin M ⊕ Fin N → ℝ) :
    ent (piMat (N := N) Sig w) x y =
      ∑ i, (((Uᵀ *ᵥ (x ∘ Sum.inl)) i * (Uᵀ *ᵥ (y ∘ Sum.inl)) i : ℝ) : ℂ) *
          (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) +
        w * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ) := by
  rw [piMat, rb_ent_blocks, rb_piBlock_eq h₂ h₁ hS hw]
  congr 1
  · change testBilin _ _ _ = _
    rw [testBilin_conj]
    simp only [testBilin, mulVec_diagonal, dotProduct, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [ent, smul_mulVec, one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun μ _ => by simp only [cvec, Function.comp_apply]; ring

/-- `⟨x, diag(Σ, 0) y⟩ = ∑ᵢ σᵢ pᵢ qᵢ`. -/
private theorem rb_real_coord {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (hS : Sig = U * diagonal σ * Uᵀ) (x y : Fin M ⊕ Fin N → ℝ) :
    x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y =
      ∑ i, σ i * ((Uᵀ *ᵥ (x ∘ Sum.inl)) i * (Uᵀ *ᵥ (y ∘ Sum.inl)) i) := by
  have e : x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y =
      (x ∘ Sum.inl) ⬝ᵥ Sig *ᵥ (y ∘ Sum.inl) := by
    simp only [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, zero_mulVec, add_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rfl
  rw [e, hS, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|Σ̲ x|² = |Uᵀ Σ x_M|² + |x_N|²` and `(Uᵀ Σ x_M)ᵢ = σᵢ (Uᵀ x_M)ᵢ`. -/
private theorem rb_testNorm_SigU {Sig U : Matrix (Fin M) (Fin M) ℝ} {σ : Fin M → ℝ}
    (h₂ : U * Uᵀ = 1) (h₁ : Uᵀ * U = 1) (hS : Sig = U * diagonal σ * Uᵀ)
    (x : Fin M ⊕ Fin N → ℝ) :
    testNorm (SigU (n := Fin N) Sig *ᵥ x) =
      √(∑ i, (σ i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i) ^ 2 + ∑ μ, x (Sum.inr μ) ^ 2) := by
  have e : ∀ i, σ i * (Uᵀ *ᵥ (x ∘ Sum.inl)) i = (Uᵀ *ᵥ (Sig *ᵥ (x ∘ Sum.inl))) i := by
    intro i
    rw [hS, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁, Matrix.one_mul,
      ← mulVec_mulVec, mulVec_diagonal]
  simp only [e, rb_sum_sq_UT h₂]
  unfold testNorm
  congr 1
  simp only [SigU, fromBlocks_mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mulVec, add_zero, zero_add, one_mulVec]
  rfl

/-- `|−⟨x, diag(Σ, 0) y⟩ − Π_{xy}| ≤ K max(c⁻¹, 1) |Σ̲x| |Σ̲y|` when `|w| ≤ K` and
`|1 + σᵢ w| ≥ c`. -/
private theorem rb_pi_part {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {c K : ℝ}
    (hc : 0 < c) {w : ℂ} (hwK : ‖w‖ ≤ K) (hOne : ∀ i, c ≤ ‖1 + (specOf Sig i : ℂ) * w‖)
    (x y : Fin M ⊕ Fin N → ℝ) :
    ‖-((x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y : ℝ) : ℂ) -
        ent (piMat (N := N) Sig w) x y‖ ≤
      K * max c⁻¹ 1 * testNorm (SigU (n := Fin N) Sig *ᵥ x) *
        testNorm (SigU (n := Fin N) Sig *ᵥ y) := by
  obtain ⟨U, h₂, h₁, hSd, hσ⟩ := rb_diag hSig
  set σ := specOf Sig with hσdef
  have hw0 : ∀ i, 1 + (σ i : ℂ) * w ≠ 0 := fun i h0 => by
    have := hOne i
    rw [h0, norm_zero] at this
    linarith
  set p := Uᵀ *ᵥ (x ∘ Sum.inl) with hp
  set q := Uᵀ *ᵥ (y ∘ Sum.inl) with hq
  have hK : 0 ≤ K := (norm_nonneg w).trans hwK
  set κ := max c⁻¹ 1 with hκ
  have hκ1 : 1 ≤ κ := le_max_right _ _
  have hκc : c⁻¹ ≤ κ := le_max_left _ _
  rw [rb_pi_coord h₂ h₁ hSd hw0, rb_real_coord hSd, rb_testNorm_SigU h₂ h₁ hSd,
    rb_testNorm_SigU h₂ h₁ hSd]
  -- the remainder as a sum of eigen-coordinates
  have e : -(((∑ i, σ i * (p i * q i) : ℝ)) : ℂ) -
      (∑ i, ((p i * q i : ℝ) : ℂ) * (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) +
        w * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)) =
      ∑ i, (((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹)) +
        (-w) * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ) := by
    have ht : ∀ i, -(((σ i * (p i * q i) : ℝ)) : ℂ) -
        ((p i * q i : ℝ) : ℂ) * (-((σ i : ℂ) * (1 + (σ i : ℂ) * w)⁻¹)) =
        (((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹)) := by
      intro i
      have := hw0 i
      push_cast
      field_simp
      ring
    rw [Complex.ofReal_sum, ← Finset.sum_congr rfl fun i _ => ht i, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
    ring
  rw [e]
  have h1 : ∀ i, ‖(((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹))‖ ≤
      K * κ * (|σ i * p i| * |σ i * q i|) := by
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_neg, norm_mul, norm_inv]
    have hpos : 0 < ‖1 + (σ i : ℂ) * w‖ := hc.trans_le (hOne i)
    have hinv : ‖1 + (σ i : ℂ) * w‖⁻¹ ≤ κ := (inv_anti₀ hc (hOne i)).trans hκc
    have : ‖w‖ * ‖1 + (σ i : ℂ) * w‖⁻¹ ≤ K * κ :=
      mul_le_mul hwK hinv (inv_nonneg.2 hpos.le) hK
    nlinarith [mul_nonneg (abs_nonneg (σ i * p i)) (abs_nonneg (σ i * q i))]
  have h2 : ‖(-w) * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)‖ ≤
      K * κ * ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| := by
    rw [norm_mul, norm_neg]
    have hs : ‖∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)‖ ≤
        ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun μ _ => ?_))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hs0 : 0 ≤ ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| :=
      Finset.sum_nonneg fun μ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hwκ : ‖w‖ ≤ K * κ := hwK.trans (le_mul_of_one_le_right hK hκ1)
    exact mul_le_mul hwκ hs (norm_nonneg _) (by positivity)
  -- Cauchy–Schwarz on `Fin M ⊕ Fin N`
  set f : Fin M ⊕ Fin N → ℝ := Sum.elim (fun i => |σ i * p i|) (fun μ => |x (Sum.inr μ)|)
  set g : Fin M ⊕ Fin N → ℝ := Sum.elim (fun i => |σ i * q i|) (fun μ => |y (Sum.inr μ)|)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  simp only [f, g, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sq_abs] at hcs
  calc _ ≤ ‖∑ i, (((σ i * p i) * (σ i * q i) : ℝ) : ℂ) * (-(w * (1 + (σ i : ℂ) * w)⁻¹))‖ +
        ‖(-w) * ∑ μ, ((x (Sum.inr μ) * y (Sum.inr μ) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ∑ i, K * κ * (|σ i * p i| * |σ i * q i|) +
        K * κ * ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)| :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => h1 i)) h2
    _ = K * κ * (∑ i, |σ i * p i| * |σ i * q i| +
        ∑ μ, |x (Sum.inr μ)| * |y (Sum.inr μ)|) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := by
        rw [mul_assoc (K * κ)]
        exact mul_le_mul_of_nonneg_left hcs (by positivity)

/-! ## The deterministic estimate of Lemma 7.12 -/

/-- (Lemma 4.10 input) The setting of §7 gives the density assumptions on `specOf Σ`. -/
private theorem rb_density {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) : DensityAssumptions τ N (specOf Sig) :=
  (IsModel.diagModel_specOf (Ω := GaussSpace M N)
    ⟨hset.ratio_ge, hset.ratio_le, (gaussX_isGaussianEnsemble M N).entryAssumption hN,
      hset.sigma⟩).densityAssumptions hset.pos

/-- `S_x = ∑_k ⟨x, u_k⟩² |λ_k − z|⁻¹`. -/
private def rbS {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (z : ℂ) (x : Fin M ⊕ Fin N → ℝ) : ℝ :=
  ∑ k, (x ⬝ᵥ rbU hSig A k) ^ 2 * ‖((rbEig hSig A k : ℂ) - z)⁻¹‖

/-- `|G_{xy} − Π_{xy}| ≤ (S_x + S_y)/2 + K_m max(c⁻¹, 1) |Σ̲x| |Σ̲y|`. -/
private theorem rb_split {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S)
    (A : Matrix (Fin M) (Fin N) ℝ) (x y : Fin M ⊕ Fin N → ℝ) :
    ‖ent (G Sig A z - PiZ N Sig z) x y‖ ≤
      (rbS hset.sigma.posDef A z x + rbS hset.sigma.posDef A z y) / 2 +
        mBoundConst τ * max c⁻¹ 1 * testNorm (SigU (n := Fin N) Sig *ᵥ x) *
          testNorm (SigU (n := Fin N) Sig *ᵥ y) := by
  have hSig := hset.sigma.posDef
  have hzD := hset.domain.1 hz
  have hm := (gen_prop_m_specDomain (rb_density hset hN) hzD).2.1
  have hpi := rb_pi_part (N := N) hSig hset.c_pos hm (hset.oneXm z hz) x y
  rw [rb_ent_sub, rb_ent_G hSig A hzD.1]
  have e : -((x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y : ℝ) : ℂ) +
      ∑ k, (((x ⬝ᵥ rbU hSig A k) * (y ⬝ᵥ rbU hSig A k) : ℝ) : ℂ) *
        ((rbEig hSig A k : ℂ) - z)⁻¹ - ent (PiZ N Sig z) x y =
      ∑ k, (((x ⬝ᵥ rbU hSig A k) * (y ⬝ᵥ rbU hSig A k) : ℝ) : ℂ) *
        ((rbEig hSig A k : ℂ) - z)⁻¹ +
      (-((x ⬝ᵥ fromBlocks Sig 0 0 (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ y : ℝ) : ℂ) -
        ent (piMat (N := N) Sig (mFun N (specOf Sig) z)) x y) := by
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hpi)
  refine (norm_sum_le _ _).trans ?_
  unfold rbS
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h0 := norm_nonneg ((rbEig hSig A k : ℂ) - z)⁻¹
  nlinarith [sq_nonneg (|x ⬝ᵥ rbU hSig A k| - |y ⬝ᵥ rbU hSig A k|), sq_abs (x ⬝ᵥ rbU hSig A k),
    sq_abs (y ⬝ᵥ rbU hSig A k),
    mul_nonneg h0 (sq_nonneg (|x ⬝ᵥ rbU hSig A k| - |y ⬝ᵥ rbU hSig A k|))]

/-- `|λ_k − E| ≤ τ⁻¹ ‖AᵀA‖ + τ⁻¹` for `z ∈ 𝐃`. -/
private theorem rb_eig_dist {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ)
    (k : Fin N) : |rbEig hset.sigma.posDef A k - z.re| ≤ τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹ := by
  have h0 := rbEig_nonneg hset.sigma.posDef A k
  have h1 := rbEig_le hset.sigma hset.pos A k
  have hE := (hset.domain.1 hz).2.2.1
  rw [abs_le] at hE ⊢
  constructor <;> linarith

/-- (Lemma 7.12, dyadic split) `S_x ≤ (6N^{2δ} + 2T) ∑_{l=1}^{L} Im G_{xx}(E + iη_l)` for
`Im z < 1`, `T = τ⁻¹‖AᵀA‖ + τ⁻¹`. -/
private theorem rb_S_ladder {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ∈ S)
    (hz1 : z.im < 1) (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) :
    rbS hset.sigma.posDef A z x ≤ (6 * (N : ℝ) ^ (2 * δ) + 2 * (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹)) *
      ∑ l ∈ Finset.Icc 1 (ladderL N δ z.im), (ent (G Sig A (ladderPt N δ z l)) x x).im := by
  have hSig := hset.sigma.posDef
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hpt : ∀ l, 0 < (ladderPt N δ z l).im := fun l =>
    hη.trans_le (ladderEta_bounds hN hδ hη hz1.le l).1
  have hG : ∀ l, (ent (G Sig A (ladderPt N δ z l)) x x).im =
      ∑ k, (x ⬝ᵥ rbU hSig A k) ^ 2 * rbKer (rbEig hSig A k - z.re) (ladderEta N δ z.im l) :=
    fun l => rb_im hSig A (hpt l) x
  simp only [hG]
  rw [Finset.sum_comm, Finset.mul_sum]
  unfold rbS
  refine Finset.sum_le_sum fun k _ => ?_
  rw [rb_inv_norm, ← Finset.mul_sum, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (rb_ladder_term hN hδ hη hz1 (rb_eig_dist hset hz A k)) (sq_nonneg _)

/-- `S_x ≤ (1 + T) Im G_{xx}(z)` for `Im z ≥ 1`, `T = τ⁻¹‖AᵀA‖ + τ⁻¹`. -/
private theorem rb_S_top {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) {z : ℂ} (hz : z ∈ S) (hz1 : 1 ≤ z.im)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) :
    rbS hset.sigma.posDef A z x ≤
      (1 + (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹)) * (ent (G Sig A z) x x).im := by
  rw [rb_im hset.sigma.posDef A (one_pos.trans_le hz1), Finset.mul_sum]
  unfold rbS
  refine Finset.sum_le_sum fun k _ => ?_
  rw [rb_inv_norm, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (rb_top_term hz1 (rb_eig_dist hset hz A k)) (sq_nonneg _)

/-! ## Lemma 7.12 -/

/-- Lemma 7.12 (`lem:rough_bound`), deterministic form for `Im z < 1` (so `L(η) ≥ 1`). -/
theorem rough_bound {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ∈ S)
    (hz1 : z.im < 1) (A : Matrix (Fin M) (Fin N) ℝ) (x y : Fin M ⊕ Fin N → ℝ) :
    ‖ent (G Sig A z - PiZ N Sig z) x y‖ ≤
      (3 * (N : ℝ) ^ (2 * δ) + τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹) *
        ∑ l ∈ Finset.Icc 1 (ladderL N δ z.im),
          ((ent (G Sig A (ladderPt N δ z l)) x x).im + (ent (G Sig A (ladderPt N δ z l)) y y).im)
      + mBoundConst τ * max c⁻¹ 1 * testNorm (SigU (n := Fin N) Sig *ᵥ x)
          * testNorm (SigU (n := Fin N) Sig *ᵥ y) := by
  have h := rb_split hset hN.le hz A x y
  have hx := rb_S_ladder hset hN hδ hz hz1 A x
  have hy := rb_S_ladder hset hN hδ hz hz1 A y
  rw [Finset.sum_add_distrib]
  have e : (6 * (N : ℝ) ^ (2 * δ) + 2 * (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹)) =
      2 * (3 * (N : ℝ) ^ (2 * δ) + τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹) := by ring
  rw [e] at hx hy
  nlinarith

/-! ## Monotonicity of Stieltjes transforms in `Im z` (proof of Lemma 7.13) -/

/-- `y ↦ y Im G_{xx}(E + iy)` is nondecreasing. -/
theorem im_ent_G_mul_mono {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (A : Matrix (Fin M) (Fin N) ℝ) (x : Fin M ⊕ Fin N → ℝ) (E : ℝ) {y₁ y₂ : ℝ} (h₁ : 0 < y₁)
    (h : y₁ ≤ y₂) :
    y₁ * (ent (G Sig A ⟨E, y₁⟩) x x).im ≤ y₂ * (ent (G Sig A ⟨E, y₂⟩) x x).im := by
  have h₂ : 0 < y₂ := h₁.trans_le h
  rw [rb_im hSig A (z := ⟨E, y₁⟩) h₁, rb_im hSig A (z := ⟨E, y₂⟩) h₂, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_left_comm, mul_left_comm y₂]
  exact mul_le_mul_of_nonneg_left (rbKer_mul_mono _ h₁ h) (sq_nonneg _)

/-- `Im m(z) = ∫ Im (x − z)⁻¹ dϱ(x)`, with the integrand integrable. -/
private theorem rb_mFun_im (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) {z : ℂ}
    (hz : 0 < z.im) :
    Integrable (fun x : ℝ => rbKer (x - z.re) z.im) (varrho N σ) ∧
      (mFun N σ z).im = ∫ x, rbKer (x - z.re) z.im ∂(varrho N σ) := by
  have := isProbabilityMeasure_varrho N σ hσ hN
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := fun x h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) (varrho N σ) := by
    refine Integrable.of_bound ?_ (z.im)⁻¹ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.sub continuous_const).inv₀ hne).aestronglyMeasurable
    · rw [rb_inv_norm]
      refine inv_anti₀ hz ?_
      calc z.im = √(z.im ^ 2) := (Real.sqrt_sq hz.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x - z.re)])
  have him : ∀ x : ℝ, RCLike.im (((x : ℂ) - z)⁻¹) = rbKer (x - z.re) z.im := fun x => by
    rw [RCLike.im_to_complex, rb_inv_im]
  refine ⟨?_, ?_⟩
  · have := hint.im
    simp only [him] at this
    exact this
  · have hres : ∀ x : ℝ, resolvent z x = ((x : ℂ) - z)⁻¹ := by
      intro x
      simp [resolvent, Ring.inverse_eq_inv']
    rw [← resolventTransform_varrho N σ hσ hN hz, resolventTransform_apply]
    simp_rw [hres]
    rw [← RCLike.im_to_complex, ← integral_im hint]
    simp only [him]

/-- `y ↦ y⁻¹ Im m(E + iy)` is nonincreasing. -/
theorem im_mFun_div_anti (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E : ℝ)
    {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h : y₁ ≤ y₂) :
    (mFun N σ ⟨E, y₂⟩).im / y₂ ≤ (mFun N σ ⟨E, y₁⟩).im / y₁ := by
  have h₂ : 0 < y₂ := h₁.trans_le h
  obtain ⟨hi₁, e₁⟩ := rb_mFun_im σ hσ hN (z := ⟨E, y₁⟩) h₁
  obtain ⟨hi₂, e₂⟩ := rb_mFun_im σ hσ hN (z := ⟨E, y₂⟩) h₂
  rw [e₁, e₂, ← integral_div, ← integral_div]
  exact integral_mono (hi₂.div_const y₂) (hi₁.div_const y₁) fun x => rbKer_div_anti _ h₁ h

/-- `y ↦ Ψ(E + iy)` is nonincreasing. -/
theorem Psi_anti (σ : Fin M → ℝ) (hσ : ∀ i, 0 ≤ σ i) (hN : 0 < N) (E : ℝ) {y₁ y₂ : ℝ}
    (h₁ : 0 < y₁) (h : y₁ ≤ y₂) : Psi N σ ⟨E, y₂⟩ ≤ Psi N σ ⟨E, y₁⟩ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := im_mFun_div_anti σ hσ hN E h₁ h
  unfold Psi
  have e : ∀ y : ℝ, (mFun N σ ⟨E, y⟩).im / (N * (⟨E, y⟩ : ℂ).im) =
      (mFun N σ ⟨E, y⟩).im / y / N := fun y => by
    simp only
    rw [div_div, mul_comm]
  rw [e y₁, e y₂]
  refine add_le_add (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hm hNr.le)) ?_
  exact one_div_le_one_div_of_le (mul_pos hNr h₁) (mul_le_mul_of_nonneg_left h hNr.le)

/-! ## Lemma 7.13 -/

/-- `η ≤ η₁ ≤ N^δ η` for `0 < η < 1`. -/
private theorem rb_eta1 {N : ℕ} (hN : 1 < N) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hη1 : η < 1) :
    η ≤ ladderEta N δ η 1 ∧ ladderEta N δ η 1 ≤ (N : ℝ) ^ δ * η := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hηN : η < (N : ℝ) ^ δ := hη1.trans (Real.one_lt_rpow hN1 hδ)
  have hL : 0 < ladderL N δ η := by
    rw [ladderL, Nat.ceil_pos]
    exact div_pos (Real.log_pos (one_lt_inv₀ hη |>.2 hη1)) (mul_pos hδ (Real.log_pos hN1))
  have he0 : ladderEta N δ η 0 = η := by simp [ladderEta, hL]
  refine ⟨(ladderEta_bounds hN hδ hη hη1.le 1).1, ?_⟩
  have := ladderEta_succ_le hN hδ hη hηN hL
  rwa [he0] at this

/-- `Σ̲ v̄ = v`. -/
private theorem rb_SigU_vbar {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (v : Fin M ⊕ Fin N → ℝ) : SigU (n := Fin N) Sig *ᵥ vbar Sig v = v := by
  have hS : Sig * Sig⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hSig.isUnit)
  funext s
  rcases s with i | μ
  · simp [SigU, vbar, fromBlocks_mulVec, mulVec_mulVec, hS]
  · simp [SigU, vbar, fromBlocks_mulVec]

private theorem rb_testNorm_smul {ι : Type*} [Fintype ι] (r : ℝ) (v : ι → ℝ) :
    testNorm (r • v) = |r| * testNorm v := by
  unfold testNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

private theorem rb_testBilin_smul {ι : Type*} [Fintype ι] (r s : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) :
    testBilin (r • v) B (s • w) = ((r * s : ℝ) : ℂ) * testBilin v B w := by
  have hw : (fun t => (((s • w) t : ℝ) : ℂ)) = (s : ℂ) • fun t => ((w t : ℝ) : ℂ) := by
    funext t; simp
  have hv : (fun t => (((r • v) t : ℝ) : ℂ)) = (r : ℂ) • fun t => ((v t : ℝ) : ℂ) := by
    funext t; simp
  unfold testBilin
  rw [hw, hv, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    Complex.ofReal_mul]
  ring

private theorem rb_testNorm_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℝ} (h : testNorm v = 0) :
    v = 0 := by
  unfold testNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h
  funext s
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (h s (Finset.mem_univ _))

/-- `Im m + N^{C₀δ} Ψ ≤ 2K_m + 2` on `𝐃` when `C₀δ ≤ τ/4`. -/
private theorem rb_K1 {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {C₀ δ : ℝ} (hC₀δ : C₀ * δ ≤ τ / 4)
    {p : ℂ} (hp : p ∈ S) :
    (mFun N (specOf Sig) p).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) p ≤
      2 * mBoundConst τ + 2 := by
  have hτ := hset.pos
  have hm := (gen_prop_m_specDomain (rb_density hset hN) (hset.domain.1 hp)).2.1
  obtain ⟨hη, -, -, hηN, -⟩ := hset.domain.1 hp
  obtain ⟨-, -, -, -, hσ⟩ := rb_diag hset.sigma.posDef
  have hm0 := (mFun_spec N _ (fun i => (hσ i).le) hη).1
  set Km := mBoundConst τ with hKm
  have hmK : (mFun N (specOf Sig) p).im ≤ Km := (Complex.im_le_norm _).trans hm
  have hKm0 : 0 ≤ Km := (norm_nonneg _).trans hm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hNη : (N : ℝ) ^ τ ≤ N * p.im := by
    have e : (N : ℝ) ^ τ = N * (N : ℝ) ^ (-1 + τ) := by
      rw [← Real.rpow_one_add' hNp.le (by linarith)]
      ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left hηN hNp.le
  have hpos : 0 < (N : ℝ) * p.im := mul_pos hNp hη
  have hq1 : (N : ℝ) ^ (C₀ * δ) ≤ (N : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hq2 : (N : ℝ) ^ (C₀ * δ) * (N : ℝ) ^ (C₀ * δ) ≤ (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hq0 : 0 ≤ (N : ℝ) ^ (C₀ * δ) := Real.rpow_nonneg hNp.le _
  have ht2 : (N : ℝ) ^ (C₀ * δ) * (1 / ((N : ℝ) * p.im)) ≤ 1 := by
    rw [mul_one_div, div_le_one hpos]
    exact hq1.trans hNη
  have ht1 : (N : ℝ) ^ (C₀ * δ) * √((mFun N (specOf Sig) p).im / ((N : ℝ) * p.im)) ≤ √Km := by
    rw [show (N : ℝ) ^ (C₀ * δ) = √((N : ℝ) ^ (C₀ * δ) * (N : ℝ) ^ (C₀ * δ)) from
      (Real.sqrt_mul_self hq0).symm, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc (N : ℝ) ^ (C₀ * δ) * (N : ℝ) ^ (C₀ * δ) * ((mFun N (specOf Sig) p).im / (N * p.im))
        ≤ (N * p.im) * ((mFun N (specOf Sig) p).im / (N * p.im)) :=
          mul_le_mul_of_nonneg_right (hq2.trans hNη) (div_nonneg hm0.le hpos.le)
      _ = (mFun N (specOf Sig) p).im := by field_simp
      _ ≤ Km := hmK
  have hsq : √Km ≤ Km + 1 := by nlinarith [Real.sq_sqrt hKm0, Real.sqrt_nonneg Km]
  unfold Psi
  rw [mul_add]
  linarith

/-- Lemma 7.13 (a_priori_1) for `Im z < 1`, deterministic part (unit `v, w`). -/
private theorem rb_ap1_ladder {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ∈ S)
    (hz1 : z.im < 1) (A : Matrix (Fin M) (Fin N) ℝ) {Cn : ℝ} (hA : ‖Aᵀ * A‖ ≤ Cn)
    (v w : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (hw : testNorm w = 1) {B : ℝ}
    (hB : ∀ l ∈ Finset.Icc 1 (ladderL N δ z.im),
      ImGvv Sig A (ladderPt N δ z l) v ≤ B ∧ ImGvv Sig A (ladderPt N δ z l) w ≤ B) :
    ‖testBilin v (lawMat Sig A z) w‖ ≤
      (3 * (N : ℝ) ^ (2 * δ) + (τ⁻¹ * Cn + τ⁻¹)) * (ladderL N δ z.im * (2 * B)) +
        mBoundConst τ * max c⁻¹ 1 := by
  have hSig := hset.sigma.posDef
  have hτ := hset.pos
  rw [← ent_vbar_eq_testBilin hSig]
  have h := rough_bound hset hN hδ hz hz1 A (vbar Sig v) (vbar Sig w)
  rw [rb_SigU_vbar hSig, rb_SigU_vbar hSig, hv, hw, mul_one, mul_one] at h
  have hη : 0 < z.im := (hset.domain.1 hz).1
  have hpt : ∀ l, 0 < (ladderPt N δ z l).im := fun l =>
    hη.trans_le (ladderEta_bounds hN hδ hη hz1.le l).1
  have hsum0 : 0 ≤ ∑ l ∈ Finset.Icc 1 (ladderL N δ z.im),
      ((ent (G Sig A (ladderPt N δ z l)) (vbar Sig v) (vbar Sig v)).im +
        (ent (G Sig A (ladderPt N δ z l)) (vbar Sig w) (vbar Sig w)).im) :=
    Finset.sum_nonneg fun l _ =>
      add_nonneg (rb_im_nonneg hSig A (hpt l) _) (rb_im_nonneg hSig A (hpt l) _)
  have hsum : ∑ l ∈ Finset.Icc 1 (ladderL N δ z.im),
      ((ent (G Sig A (ladderPt N δ z l)) (vbar Sig v) (vbar Sig v)).im +
        (ent (G Sig A (ladderPt N δ z l)) (vbar Sig w) (vbar Sig w)).im) ≤
      ladderL N δ z.im * (2 * B) := by
    refine (Finset.sum_le_sum fun l hl => (?_ : _ ≤ 2 * B)).trans ?_
    · have := hB l hl
      exact (add_le_add this.1 this.2).trans_eq (two_mul B).symm
    · rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hτi : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
  have hc0 : 0 ≤ 3 * (N : ℝ) ^ (2 * δ) + τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹ := by
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (2 * δ)
    have := mul_nonneg hτi (norm_nonneg (Aᵀ * A))
    linarith
  have hc1 : 3 * (N : ℝ) ^ (2 * δ) + τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹ ≤
      3 * (N : ℝ) ^ (2 * δ) + (τ⁻¹ * Cn + τ⁻¹) := by
    have := mul_le_mul_of_nonneg_left hA hτi
    linarith
  exact h.trans (add_le_add (mul_le_mul hc1 hsum hsum0 (hc0.trans hc1)) le_rfl)

/-- Lemma 7.13 (a_priori_1) for `Im z ≥ 1`, deterministic part (unit `v, w`). -/
private theorem rb_ap1_top {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 ≤ N) {z : ℂ} (hz : z ∈ S) (hz1 : 1 ≤ z.im)
    (A : Matrix (Fin M) (Fin N) ℝ) {Cn : ℝ} (hA : ‖Aᵀ * A‖ ≤ Cn)
    (v w : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (hw : testNorm w = 1) {B : ℝ}
    (hBv : ImGvv Sig A z v ≤ B) (hBw : ImGvv Sig A z w ≤ B) :
    ‖testBilin v (lawMat Sig A z) w‖ ≤ (1 + (τ⁻¹ * Cn + τ⁻¹)) * B + mBoundConst τ * max c⁻¹ 1 := by
  have hSig := hset.sigma.posDef
  have hτ := hset.pos
  rw [← ent_vbar_eq_testBilin hSig]
  have h := rb_split hset hN hz A (vbar Sig v) (vbar Sig w)
  rw [rb_SigU_vbar hSig, rb_SigU_vbar hSig, hv, hw, mul_one, mul_one] at h
  have hx := rb_S_top hset hz hz1 A (vbar Sig v)
  have hy := rb_S_top hset hz hz1 A (vbar Sig w)
  have hη : 0 < z.im := one_pos.trans_le hz1
  have hGv := rb_im_nonneg hSig A hη (vbar Sig v)
  have hGw := rb_im_nonneg hSig A hη (vbar Sig w)
  have hτi : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
  have hc0 : 0 ≤ 1 + (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹) := by
    have := mul_nonneg hτi (norm_nonneg (Aᵀ * A)); linarith
  have hc1 : 1 + (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹) ≤ 1 + (τ⁻¹ * Cn + τ⁻¹) := by
    have := mul_le_mul_of_nonneg_left hA hτi; linarith
  have h1 : (1 + (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹)) * (ent (G Sig A z) (vbar Sig v) (vbar Sig v)).im ≤
      (1 + (τ⁻¹ * Cn + τ⁻¹)) * B := mul_le_mul hc1 hBv hGv (hc0.trans hc1)
  have h2 : (1 + (τ⁻¹ * ‖Aᵀ * A‖ + τ⁻¹)) * (ent (G Sig A z) (vbar Sig w) (vbar Sig w)).im ≤
      (1 + (τ⁻¹ * Cn + τ⁻¹)) * B := mul_le_mul hc1 hBw hGw (hc0.trans hc1)
  linarith

/-- Intersection of the events used in Lemma 7.13: one event and two events per point
of `P`, `2|P| + 1 ≤ N`. -/
private theorem rb_events {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 1 ≤ N) {D : ℝ}
    (P : Finset ℂ) (hcard : 2 * P.card + 1 ≤ N) (F₀ : Set Ω) (h₀ : HighProbAt N D F₀)
    (F : Bool → ℂ → Set Ω) (hF : ∀ b, ∀ p ∈ P, HighProbAt N D (F b p)) :
    HighProbAt N (D - 1) {ω | ω ∈ F₀ ∧ ∀ p ∈ P, ω ∈ F true p ∧ ω ∈ F false p} := by
  set s : Finset (Option (Bool × ℂ)) := Finset.insertNone (Finset.univ ×ˢ P) with hs
  set E : Option (Bool × ℂ) → Set Ω := fun i => Option.elim i F₀ (fun bp => F bp.1 bp.2)
  have hsc : (s.card : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
    rw [hs, Finset.card_insertNone, Finset.card_product, Finset.card_univ, Fintype.card_bool,
      Real.rpow_one]
    exact_mod_cast (by omega : 2 * P.card + 1 ≤ N)
  have h := HighProbAt.biInter s hN hsc (A := E) (D := D - 1) (fun i hi => by
    rw [sub_add_cancel]
    rcases i with _ | ⟨b, p⟩
    · exact h₀
    · exact hF b p (Finset.mem_product.1 (Finset.some_mem_insertNone.1 hi)).2)
  unfold HighProbAt at h ⊢
  refine le_trans (measure_mono (Set.compl_subset_compl.2 fun ω hω => ?_)) h
  have hω' := Set.mem_iInter₂.1 hω
  refine ⟨hω' none Finset.none_mem_insertNone, fun p hp => ⟨?_, ?_⟩⟩
  · exact hω' (some (true, p))
      (Finset.some_mem_insertNone.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hp⟩))
  · exact hω' (some (false, p))
      (Finset.some_mem_insertNone.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hp⟩))

/-- The points at which (A_{m−1}) is used: the ladder `E + iη_l`, `1 ≤ l ≤ L`, for `Im z < 1`;
`z` itself otherwise. -/
private def rbPts (N : ℕ) (δ : ℝ) (z : ℂ) : Finset ℂ :=
  if z.im < 1 then (Finset.Icc 1 (ladderL N δ z.im)).image (ladderPt N δ z) else {z}

private theorem rbPts_of_lt {N : ℕ} {δ : ℝ} {z : ℂ} (h : z.im < 1) :
    rbPts N δ z = (Finset.Icc 1 (ladderL N δ z.im)).image (ladderPt N δ z) := by
  simp only [rbPts, h, ↓reduceIte]

private theorem rbPts_of_ge {N : ℕ} {δ : ℝ} {z : ℂ} (h : ¬ z.im < 1) : rbPts N δ z = {z} := by
  simp only [rbPts, h, ↓reduceIte]

/-- Exponent bookkeeping of (a_priori_1) for `Im z < 1`. -/
private theorem rb_num_ladder {a2 e T₀ K₁ Kmκ L δi X : ℝ} (ha2 : 1 ≤ a2) (he : 1 ≤ e)
    (hT₀ : 0 ≤ T₀) (hK₁ : 0 ≤ K₁) (hKmκ : 0 ≤ Kmκ) (hL0 : 0 ≤ L) (hL : L ≤ δi + 1)
    (hK₂ : (3 + T₀) * (2 * (δi + 1)) * K₁ + Kmκ ≤ e)
    (hX : X ≤ (3 * a2 + T₀) * (L * (2 * (e * K₁))) + Kmκ) : X ≤ e * e * a2 := by
  have hx : 3 * a2 + T₀ ≤ (3 + T₀) * a2 := by nlinarith
  have hy : L * (2 * (e * K₁)) ≤ (δi + 1) * (2 * (e * K₁)) :=
    mul_le_mul_of_nonneg_right hL (by positivity)
  have h1 : (3 * a2 + T₀) * (L * (2 * (e * K₁))) ≤
      a2 * e * ((3 + T₀) * (2 * (δi + 1)) * K₁) := by
    calc _ ≤ ((3 + T₀) * a2) * ((δi + 1) * (2 * (e * K₁))) :=
          mul_le_mul hx hy (by positivity) (by positivity)
      _ = _ := by ring
  have h2 : Kmκ ≤ a2 * e * Kmκ := le_mul_of_one_le_left hKmκ (one_le_mul_of_one_le_of_one_le ha2 he)
  have h3 : a2 * e * ((3 + T₀) * (2 * (δi + 1)) * K₁ + Kmκ) ≤ a2 * e * e :=
    mul_le_mul_of_nonneg_left hK₂ (by positivity)
  nlinarith

/-- Exponent bookkeeping of (a_priori_1) for `Im z ≥ 1`. -/
private theorem rb_num_top {a2 e T₀ K₁ Kmκ δi X : ℝ} (ha2 : 1 ≤ a2) (he : 1 ≤ e)
    (hT₀ : 0 ≤ T₀) (hK₁ : 0 ≤ K₁) (hKmκ : 0 ≤ Kmκ) (hδi : 0 < δi)
    (hK₂ : (3 + T₀) * (2 * (δi + 1)) * K₁ + Kmκ ≤ e)
    (hX : X ≤ (1 + T₀) * (e * K₁) + Kmκ) : X ≤ e * e * a2 := by
  have hx : 1 + T₀ ≤ (3 + T₀) * (2 * (δi + 1)) := by nlinarith [hδi]
  have h1 : (1 + T₀) * (e * K₁) ≤ e * ((3 + T₀) * (2 * (δi + 1)) * K₁) := by
    calc _ ≤ ((3 + T₀) * (2 * (δi + 1))) * (e * K₁) :=
          mul_le_mul_of_nonneg_right hx (by positivity)
      _ = _ := by ring
  have h2 : Kmκ ≤ e * Kmκ := le_mul_of_one_le_left hKmκ he
  have h3 : e * ((3 + T₀) * (2 * (δi + 1)) * K₁ + Kmκ) ≤ e * e :=
    mul_le_mul_of_nonneg_left hK₂ (by positivity)
  have h4 : e * e ≤ e * e * a2 := le_mul_of_one_le_right (by positivity) ha2
  nlinarith

/-- Lemma 7.13 (a_priori_1), deterministic part: on the event where `‖AᵀA‖ ≤ C_n` and
`Im G_{v̄v̄}, Im G_{w̄w̄} ≤ N^{ε_A} K₁` at the points `rbPts`, `|⟨v, Σ̲⁻¹(G − Π)Σ̲⁻¹ w⟩| ≤
N^{2ε_A} N^{2δ}` for unit `v, w`. -/
private theorem rb_ap1_det {τ c : ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    (hset : CompSetting τ c M N Sig S) (hN : 1 < N) {δ εA : ℝ} (hδ : 0 < δ) (hεA : 0 < εA)
    {z : ℂ} (hz : z ∈ S) (A : Matrix (Fin M) (Fin N) ℝ) {Cn : ℝ} (hXX : ‖Aᵀ * A‖ ≤ max Cn 0)
    (v w : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) (hw : testNorm w = 1)
    (hNK : (3 + (τ⁻¹ * max Cn 0 + τ⁻¹)) * (2 * (δ⁻¹ + 1)) * (2 * mBoundConst τ + 2) +
      mBoundConst τ * max c⁻¹ 1 ≤ (N : ℝ) ^ εA)
    (hBK : ∀ p ∈ rbPts N δ z, ImGvv Sig A p v ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2) ∧
      ImGvv Sig A p w ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2)) :
    ‖testBilin v (lawMat Sig A z) w‖ ≤ (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) := by
  have hτ := hset.pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hKm0 : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
  have hN2ε : (N : ℝ) ^ (2 * εA) = (N : ℝ) ^ εA * (N : ℝ) ^ εA := by
    rw [← Real.rpow_add hNp]; ring_nf
  have ha2 : 1 ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hNr.le (by positivity)
  have he : 1 ≤ (N : ℝ) ^ εA := Real.one_le_rpow hNr.le hεA.le
  have hT₀ : 0 ≤ τ⁻¹ * max Cn 0 + τ⁻¹ := by
    have := inv_pos.2 hτ; have := le_max_right Cn 0; positivity
  have hKmκ : 0 ≤ mBoundConst τ * max c⁻¹ 1 :=
    mul_nonneg hKm0.le (zero_le_one.trans (le_max_right _ _))
  have hK₁ : 0 ≤ 2 * mBoundConst τ + 2 := by positivity
  rw [hN2ε]
  by_cases hη1 : z.im < 1
  · have hB : ∀ l ∈ Finset.Icc 1 (ladderL N δ z.im),
        ImGvv Sig A (ladderPt N δ z l) v ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2) ∧
          ImGvv Sig A (ladderPt N δ z l) w ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2) :=
      fun l hl => hBK _ (by rw [rbPts_of_lt hη1]; exact Finset.mem_image_of_mem _ hl)
    have h := rb_ap1_ladder hset hN hδ hz hη1 A hXX v w hv hw hB
    have hηN : (N : ℝ) ^ (-1 : ℝ) ≤ z.im :=
      (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)).trans (hset.domain.1 hz).2.2.2.1
    exact rb_num_ladder ha2 he hT₀ hK₁ hKmκ (Nat.cast_nonneg _) (ladderL_le hN hδ hηN) hNK h
  · have hzP : z ∈ rbPts N δ z := by rw [rbPts_of_ge hη1]; exact Finset.mem_singleton_self z
    have h := rb_ap1_top hset hN.le hz (not_lt.1 hη1) A hXX v w hv hw (hBK z hzP).1 (hBK z hzP).2
    exact rb_num_top ha2 he hT₀ hK₁ hKmκ (inv_pos.2 hδ) hNK h

/-- Lemma 7.13 (a_priori_1) at one `z ∈ S_m`. -/
private theorem rb_ap1 {τ c : ℝ} {C : ℕ → ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    {P : ModelClass M N} {C₀ δ εA DA : ℝ} {m : ℕ} (hset : CompSetting τ c M N Sig S)
    (hN : 1 < N) (hτ1 : τ ≤ 1) (hδ : 0 < δ) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) (hm : 1 ≤ m)
    (hA : PropA N C P Sig S C₀ δ (m - 1) εA DA) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (hX : EntryAssumption C X) (hP : P Ω X) {z : ℂ} (hz : z ∈ levelSet N δ S m) {Cn : ℝ}
    (hnorm : HighProbAt N DA {ω | ‖(X ω)ᵀ * X ω‖ ≤ Cn}) (hNc : 2 * δ⁻¹ + 3 ≤ (N : ℝ))
    (hNK : (3 + (τ⁻¹ * max Cn 0 + τ⁻¹)) * (2 * (δ⁻¹ + 1)) * (2 * mBoundConst τ + 2) +
      mBoundConst τ * max c⁻¹ 1 ≤ (N : ℝ) ^ εA)
    (v w : Fin M ⊕ Fin N → ℝ) :
    DomAt N (2 * εA) (DA - 1) (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖)
      (fun _ => (N : ℝ) ^ (2 * δ) * testNorm v * testNorm w) := by
  have hN1' : 1 ≤ N := hN.le
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hzS := hz.1
  have hzD := hset.domain.1 hzS
  by_cases h0 : testNorm v = 0 ∨ testNorm w = 0
  · have hξ : ∀ ω, ‖testBilin v (lawMat Sig (X ω) z) w‖ = 0 := by
      intro ω
      rcases h0 with h0 | h0
      · rw [rb_testNorm_eq_zero h0]; simp [testBilin, dotProduct, mulVec]
      · rw [rb_testNorm_eq_zero h0]; simp [testBilin, dotProduct, mulVec]
    unfold DomAt
    have he : {ω | (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm v * testNorm w) <
        ‖testBilin v (lawMat Sig (X ω) z) w‖} = ∅ := by
      ext ω
      simp only [hξ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rcases h0 with h0 | h0 <;> simp [h0]
    rw [he, measure_empty]
    exact bot_le
  push Not at h0
  obtain ⟨hva, hwb⟩ := h0
  set a := testNorm v with ha
  set b := testNorm w with hb
  have ha0 : 0 < a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hva)
  have hb0 : 0 < b := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hwb)
  set v' := a⁻¹ • v with hv'
  set w' := b⁻¹ • w with hw'
  have hv1 : testNorm v' = 1 := by
    rw [hv', rb_testNorm_smul, abs_of_pos (inv_pos.2 ha0), ← ha, inv_mul_cancel₀ ha0.ne']
  have hw1 : testNorm w' = 1 := by
    rw [hw', rb_testNorm_smul, abs_of_pos (inv_pos.2 hb0), ← hb, inv_mul_cancel₀ hb0.ne']
  have hav : a • v' = v := by rw [hv', smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]
  have hbw : b • w' = w := by rw [hw', smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
  have hξ : ∀ ω, ‖testBilin v (lawMat Sig (X ω) z) w‖ =
      a * b * ‖testBilin v' (lawMat Sig (X ω) z) w'‖ := by
    intro ω
    have := rb_testBilin_smul a b v' (lawMat Sig (X ω) z) w'
    rw [hav, hbw] at this
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos ha0 hb0)]
  have hPtsLev : ∀ p ∈ rbPts N δ z, p ∈ levelSet N δ S (m - 1) := by
    intro p hp
    by_cases hη1 : z.im < 1
    · rw [rbPts_of_lt hη1, Finset.mem_image] at hp
      obtain ⟨l, hl, rfl⟩ := hp
      exact ladderPt_level hset.domain hτ1 hN hδ hm hz hη1.le (Finset.mem_Icc.1 hl).1
    · rw [rbPts_of_ge hη1, Finset.mem_singleton] at hp
      rw [hp]
      exact ⟨hzS, (Real.rpow_le_one_of_one_le_of_nonpos hNr.le
        (neg_nonpos.2 (mul_nonneg hδ.le (Nat.cast_nonneg _)))).trans (not_lt.1 hη1)⟩
  have hcard : 2 * (rbPts N δ z).card + 1 ≤ N := by
    have hc : ((rbPts N δ z).card : ℝ) ≤ δ⁻¹ + 1 := by
      by_cases hη1 : z.im < 1
      · rw [rbPts_of_lt hη1]
        have hηN : (N : ℝ) ^ (-1 : ℝ) ≤ z.im :=
          (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith [hset.pos])).trans hzD.2.2.2.1
        refine le_trans ?_ (ladderL_le hN hδ hηN)
        have := Finset.card_image_le (s := Finset.Icc 1 (ladderL N δ z.im)) (f := ladderPt N δ z)
        rw [Nat.card_Icc, Nat.add_sub_cancel] at this
        exact_mod_cast this
      · rw [rbPts_of_ge hη1, Finset.card_singleton, Nat.cast_one]
        linarith [inv_pos.2 hδ]
    have : (2 * (rbPts N δ z).card + 1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set Bp : ℂ → ℝ := fun p =>
    (mFun N (specOf Sig) p).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) p with hBp
  set u : Bool → Fin M ⊕ Fin N → ℝ := fun b => if b then v' else w' with hu
  have hu1 : ∀ b, testNorm (u b) = 1 := fun b => by cases b <;> simp [hu, hv1, hw1]
  have hE := rb_events hN1' (rbPts N δ z) hcard {ω | ‖(X ω)ᵀ * X ω‖ ≤ Cn} hnorm
    (fun b p => {ω | ImGvv Sig (X ω) p (u b) ≤ (N : ℝ) ^ εA * Bp p}) (fun b p hp => by
      have h := hA Ω X hX hP p (hPtsLev p hp) (u b) (hu1 b)
      unfold DomAt at h
      unfold HighProbAt
      convert h using 2
      ext ω
      simp [not_le, hBp])
  unfold HighProbAt at hE
  unfold DomAt
  refine le_trans (measure_mono fun ω hω => ?_) hE
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  rintro ⟨hω₀, hωP⟩
  have hNε0 : 0 ≤ (N : ℝ) ^ εA := Real.rpow_nonneg (by linarith) _
  have hBK : ∀ p ∈ rbPts N δ z, ImGvv Sig (X ω) p v' ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2) ∧
      ImGvv Sig (X ω) p w' ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2) := by
    intro p hp
    have hK' : (N : ℝ) ^ εA * Bp p ≤ (N : ℝ) ^ εA * (2 * mBoundConst τ + 2) :=
      mul_le_mul_of_nonneg_left (rb_K1 hset hN1' hC₀δ (hPtsLev p hp).1) hNε0
    exact ⟨((hωP p hp).1 : _).trans hK', ((hωP p hp).2 : _).trans hK'⟩
  have hdet := rb_ap1_det hset hN hδ hεA hzS (X ω) (hω₀.trans (le_max_left _ _)) v' w' hv1 hw1
    hNK hBK
  rw [hξ] at hω
  have := mul_le_mul_of_nonneg_left hdet (mul_pos ha0 hb0).le
  nlinarith

/-- Lemma 7.13 (a_priori_2) at one `z ∈ S_m`. -/
private theorem rb_ap2 {τ c : ℝ} {C : ℕ → ℝ} {Sig : Matrix (Fin M) (Fin M) ℝ} {S : Set ℂ}
    {P : ModelClass M N} {C₀ δ εA DA : ℝ} {m : ℕ} (hset : CompSetting τ c M N Sig S)
    (hN : 1 < N) (hτ1 : τ ≤ 1) (hδ : 0 < δ) (hm : 1 ≤ m)
    (hA : PropA N C P Sig S C₀ δ (m - 1) εA DA) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (hX : EntryAssumption C X) (hP : P Ω X) {z : ℂ} (hz : z ∈ levelSet N δ S m)
    (v : Fin M ⊕ Fin N → ℝ) (hv : testNorm v = 1) :
    DomAt N εA DA (fun ω => ImGvv Sig (X ω) z v)
      (fun _ => (N : ℝ) ^ (2 * δ) *
        ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hSig := hset.sigma.posDef
  obtain ⟨-, -, -, -, hσ⟩ := rb_diag hSig
  have hσ0 : ∀ i, 0 ≤ specOf Sig i := fun i => (hσ i).le
  have hη : 0 < z.im := (hset.domain.1 hz.1).1
  have hNδ : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hNr.le hδ.le
  have hN2δ : (N : ℝ) ^ (2 * δ) = (N : ℝ) ^ δ * (N : ℝ) ^ δ := by
    rw [← Real.rpow_add hNp]; ring_nf
  have hNε0 : 0 ≤ (N : ℝ) ^ εA := Real.rpow_nonneg hNp.le _
  have hq0 : 0 ≤ (N : ℝ) ^ (C₀ * δ) := Real.rpow_nonneg hNp.le _
  have hΨ0 : 0 ≤ Psi N (specOf Sig) z := by
    unfold Psi
    have : 0 < (N : ℝ) * z.im := mul_pos hNp hη
    positivity
  have hm0 := (mFun_spec N _ hσ0 hη).1
  set Q := (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg hq0 hΨ0
  by_cases hη1 : z.im < 1
  · obtain ⟨hη₁, hη₁N⟩ := rb_eta1 hN hδ hη hη1
    have hz₁ : ladderPt N δ z 1 ∈ levelSet N δ S (m - 1) :=
      ladderPt_level hset.domain hτ1 hN hδ hm hz hη1.le le_rfl
    have hmI : (mFun N (specOf Sig) (ladderPt N δ z 1)).im ≤
        (N : ℝ) ^ δ * (mFun N (specOf Sig) z).im := by
      have h0 : (mFun N (specOf Sig) (ladderPt N δ z 1)).im / ladderEta N δ z.im 1 ≤
          (mFun N (specOf Sig) z).im / z.im := by
        have := im_mFun_div_anti (N := N) (specOf Sig) hσ0 (by omega) z.re hη hη₁
        rw [Complex.eta] at this
        exact this
      rw [div_le_div_iff₀ (hη.trans_le hη₁) hη] at h0
      have h4 : (mFun N (specOf Sig) (ladderPt N δ z 1)).im * z.im ≤
          ((N : ℝ) ^ δ * (mFun N (specOf Sig) z).im) * z.im := by
        nlinarith [mul_le_mul_of_nonneg_left hη₁N hm0.le]
      exact le_of_mul_le_mul_right h4 hη
    have hΨ : Psi N (specOf Sig) (ladderPt N δ z 1) ≤ Psi N (specOf Sig) z := by
      have := Psi_anti (N := N) (specOf Sig) hσ0 (by omega) z.re hη hη₁
      rw [Complex.eta] at this
      exact this
    have hB1 : (mFun N (specOf Sig) (ladderPt N δ z 1)).im +
        (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) (ladderPt N δ z 1) ≤
        (N : ℝ) ^ δ * ((mFun N (specOf Sig) z).im + Q) := by
      have := mul_le_mul_of_nonneg_left hΨ hq0
      nlinarith
    have h := hA Ω X hX hP _ hz₁ v hv
    unfold DomAt at h ⊢
    refine le_trans (measure_mono fun ω hω => ?_) h
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hle
    push Not at hle
    have hmono : z.im * ImGvv Sig (X ω) z v ≤
        ladderEta N δ z.im 1 * ImGvv Sig (X ω) (ladderPt N δ z 1) v := by
      have := im_ent_G_mul_mono hSig (X ω) (vbar Sig v) z.re hη hη₁
      rw [Complex.eta] at this
      exact this
    have hG1 : 0 ≤ ImGvv Sig (X ω) (ladderPt N δ z 1) v :=
      rb_im_nonneg hSig (X ω) (hη.trans_le hη₁) _
    have hGz : ImGvv Sig (X ω) z v ≤ (N : ℝ) ^ δ * ImGvv Sig (X ω) (ladderPt N δ z 1) v := by
      have h2 := mul_le_mul_of_nonneg_right hη₁N hG1
      have h3 : z.im * ImGvv Sig (X ω) z v ≤
          z.im * ((N : ℝ) ^ δ * ImGvv Sig (X ω) (ladderPt N δ z 1) v) := by nlinarith
      exact le_of_mul_le_mul_left h3 hη
    have hfin : ImGvv Sig (X ω) z v ≤
        (N : ℝ) ^ εA * ((N : ℝ) ^ (2 * δ) * ((mFun N (specOf Sig) z).im + Q)) := by
      calc ImGvv Sig (X ω) z v ≤ (N : ℝ) ^ δ * ImGvv Sig (X ω) (ladderPt N δ z 1) v := hGz
        _ ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ εA * ((mFun N (specOf Sig) (ladderPt N δ z 1)).im +
            (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) (ladderPt N δ z 1))) :=
            mul_le_mul_of_nonneg_left hle (by linarith)
        _ ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ εA * ((N : ℝ) ^ δ * ((mFun N (specOf Sig) z).im + Q))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB1 hNε0) (by linarith)
        _ = _ := by rw [hN2δ]; ring
    linarith
  · have hzl : z ∈ levelSet N δ S (m - 1) :=
      ⟨hz.1, (Real.rpow_le_one_of_one_le_of_nonpos hNr.le
        (neg_nonpos.2 (mul_nonneg hδ.le (Nat.cast_nonneg _)))).trans (not_lt.1 hη1)⟩
    have h := hA Ω X hX hP z hzl v hv
    have hB : 0 ≤ (mFun N (specOf Sig) z).im + Q := add_nonneg hm0.le hQ0
    have hN2δ1 : 1 ≤ (N : ℝ) ^ (2 * δ) := by rw [hN2δ]; nlinarith
    exact DomAt.mono hN.le (fun _ => le_rfl) (fun _ => le_mul_of_one_le_left hB hN2δ1)
      (fun _ => mul_nonneg (by linarith) hB) le_rfl le_rfl h

/-- Lemma 7.13 at a general `C₀` with `C₀ δ ≤ τ/4`. -/
private theorem rb_cor (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m,
          (∀ v w : Fin M ⊕ Fin N → ℝ, DomAt N (2 * εA) (DA - 1)
            (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖)
            (fun _ => (N : ℝ) ^ (2 * δ) * testNorm v * testNorm w)) ∧
          (∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 → DomAt N εA DA
            (fun ω => ImGvv Sig (X ω) z v)
            (fun _ => (N : ℝ) ^ (2 * δ) *
              ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z))) := by
  obtain ⟨Cn, hCn⟩ := norm_XtX_le hτ hτ1
  obtain ⟨N₁, hN₁⟩ := hCn C DA
  set K₂ := (3 + (τ⁻¹ * max Cn 0 + τ⁻¹)) * (2 * (δ⁻¹ + 1)) * (2 * mBoundConst τ + 2) +
    mBoundConst τ * max c⁻¹ 1 with hK₂
  have hK₂0 : 0 ≤ K₂ := by
    have := inv_pos.2 hτ
    have := inv_pos.2 hδ
    have := le_max_right Cn 0
    have := le_max_right c⁻¹ 1
    have : 0 < mBoundConst τ := by unfold mBoundConst genPropConst; positivity
    rw [hK₂]; positivity
  refine ⟨max (max N₁ 2) (max ⌈2 * δ⁻¹ + 3⌉₊ ⌈K₂ ^ εA⁻¹⌉₊), ?_⟩
  intro N hN M Sig S P m hset hm hA Ω _ _ X hX hP z hz
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : 1 < N := by omega
  have hNp : (0 : ℝ) < N := by
    have : (1 : ℝ) < N := by exact_mod_cast hN1
    linarith
  have hNc : 2 * δ⁻¹ + 3 ≤ (N : ℝ) := by
    have h0 : ⌈2 * δ⁻¹ + 3⌉₊ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast h0)
  have hNK : K₂ ≤ (N : ℝ) ^ εA := by
    have h0 : ⌈K₂ ^ εA⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have h1 : K₂ ^ εA⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h0)
    calc K₂ = (K₂ ^ εA⁻¹) ^ εA := (Real.rpow_inv_rpow hK₂0 hεA.ne').symm
      _ ≤ (N : ℝ) ^ εA := Real.rpow_le_rpow (Real.rpow_nonneg hK₂0 _) h1 hεA.le
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hset.ratio_le
    rwa [div_le_iff₀ hNp] at this
  have hnorm := hN₁ N hNN₁ M X hX hM
  exact ⟨fun v w => rb_ap1 hset hN1 hτ1 hδ hC₀δ hεA hm hA X hX hP hz hnorm hNc hNK v w,
    fun v hv => rb_ap2 hset hN1 hτ1 hδ hm hA X hX hP hz v hv⟩

/-- Lemma 7.13 (`cor:rough_bound`) at a general `C₀ ≥ 25` with `C₀ δ ≤ τ/4`. -/
theorem cor_rough_bound' (τ c : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc : 0 < c) (hδ : 0 < δ) (hC₀ : 25 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting τ c M N Sig S → 1 ≤ m →
      PropA N C P Sig S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption C X → P Ω X →
        ∀ z ∈ levelSet N δ S m,
          (∀ v w : Fin M ⊕ Fin N → ℝ, DomAt N (2 * εA) (DA - 1)
            (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖)
            (fun _ => (N : ℝ) ^ (2 * δ) * testNorm v * testNorm w)) ∧
          (∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 → DomAt N εA DA
            (fun ω => ImGvv Sig (X ω) z v)
            (fun _ => (N : ℝ) ^ (2 * δ) *
              ((mFun N (specOf Sig) z).im + (N : ℝ) ^ (C₀ * δ) * Psi N (specOf Sig) z))) :=
  -- `25 ≤ C₀` is not needed here; only `C₀ δ ≤ τ / 4` enters.
  have _ := hC₀
  rb_cor τ c C C₀ δ εA DA hτ hτ1 hc hδ hC₀δ hεA


/-! ## Instances

`M = N = 2`, `Σ = 1`, `τ = 1/2`. For Lemma 7.12 the spectral domain is
`S₀ = {z ∈ 𝐃(1/2, 2) : Re z = 0, Im z ≥ 3/4}`, on which (1+xm) holds with
`c₀ = (3/4) K_m⁻¹` since `|1 + m| ≥ Im m ≥ K_m⁻¹ Im z`; the point is `z₀ = 3i/4`
(`Im z₀ < 1`, so the ladder is nonempty). -/

/-- `y ↦ y Im G_{xx}(E + iy)` at `M = N = 2`, `Σ = 1`, `X = 0`, `E = 0`, `y = 1 ≤ 2`. -/
example (x : Fin 2 ⊕ Fin 2 → ℝ) :
    1 * (ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) ⟨0, 1⟩) x x).im ≤
      2 * (ent (G (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) ⟨0, 2⟩) x x).im :=
  im_ent_G_mul_mono Matrix.PosDef.one 0 x 0 one_pos one_le_two

/-- `y ↦ y⁻¹ Im m(E + iy)` at `M = N = 2`, `σ = (1, 1)`, `E = 0`, `y = 1 ≤ 2`. -/
example : (mFun 2 (fun _ : Fin 2 => (1 : ℝ)) ⟨0, 2⟩).im / 2 ≤
    (mFun 2 (fun _ : Fin 2 => (1 : ℝ)) ⟨0, 1⟩).im / 1 :=
  im_mFun_div_anti _ (fun _ => zero_le_one) (by norm_num) 0 one_pos one_le_two

/-- `y ↦ Ψ(E + iy)` at `M = N = 2`, `σ = (1, 1)`, `E = 0`, `y = 1 ≤ 2`. -/
example : Psi 2 (fun _ : Fin 2 => (1 : ℝ)) ⟨0, 2⟩ ≤ Psi 2 (fun _ : Fin 2 => (1 : ℝ)) ⟨0, 1⟩ :=
  Psi_anti _ (fun _ => zero_le_one) (by norm_num) 0 one_pos one_le_two

/-- Lemma 7.13 at `τ = 1/2`, `c = 1`, `C = 2`, `C₀ = 25`, `δ = 1/200` (`C₀ δ = τ/4`),
`ε_A = 1/800`, `D_A = 3`. The setting, (A_{m−1}) and the class are hypotheses of the statement
(conditional in them). -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N) (m : ℕ), CompSetting (1 / 2) 1 M N Sig S → 1 ≤ m →
      PropA N (fun _ => 2) P Sig S 25 (1 / 200) (m - 1) (1 / 800) 3 →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (1 / 200) S m,
          (∀ v w : Fin M ⊕ Fin N → ℝ, DomAt N (2 * (1 / 800)) (3 - 1)
            (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖)
            (fun _ => (N : ℝ) ^ (2 * (1 / 200 : ℝ)) * testNorm v * testNorm w)) ∧
          (∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 → DomAt N (1 / 800) 3
            (fun ω => ImGvv Sig (X ω) z v)
            (fun _ => (N : ℝ) ^ (2 * (1 / 200 : ℝ)) *
              ((mFun N (specOf Sig) z).im +
                (N : ℝ) ^ (25 * (1 / 200 : ℝ)) * Psi N (specOf Sig) z))) :=
  cor_rough_bound' (1 / 2) 1 (fun _ => 2) 25 (1 / 200) (1 / 800) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Lemma 7.13 at `m = 1` with (A_0) supplied by Lemma 7.3 (`propA_zero`), at the parameters
above: the only remaining hypotheses are the setting and the class. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (S : Set ℂ)
      (P : ModelClass M N), CompSetting (1 / 2) 1 M N Sig S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (X : Ω → Matrix (Fin M) (Fin N) ℝ), EntryAssumption (fun _ => 2) X → P Ω X →
        ∀ z ∈ levelSet N (1 / 200) S 1,
          (∀ v w : Fin M ⊕ Fin N → ℝ, DomAt N (2 * (1 / 800)) (3 - 1)
            (fun ω => ‖testBilin v (lawMat Sig (X ω) z) w‖)
            (fun _ => (N : ℝ) ^ (2 * (1 / 200 : ℝ)) * testNorm v * testNorm w)) ∧
          (∀ v : Fin M ⊕ Fin N → ℝ, testNorm v = 1 → DomAt N (1 / 800) 3
            (fun ω => ImGvv Sig (X ω) z v)
            (fun _ => (N : ℝ) ^ (2 * (1 / 200 : ℝ)) *
              ((mFun N (specOf Sig) z).im +
                (N : ℝ) ^ ((25 : ℝ) * (1 / 200 : ℝ)) * Psi N (specOf Sig) z))) := by
  obtain ⟨N₀, h₀⟩ := propA_zero (1 / 2) 1 (fun _ => 2) (1 / 800) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨N₁, h₁⟩ := cor_rough_bound' (1 / 2) 1 (fun _ => 2) 25 (1 / 200) (1 / 800) 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨max N₀ N₁, fun N hN M Sig S P hset Ω _ _ X hX hP z hz => ?_⟩
  exact h₁ N (le_of_max_le_right hN) M Sig S P 1 hset le_rfl
    (h₀ N (le_of_max_le_left hN) M Sig S P 25 (1 / 200) hset (by norm_num) (by norm_num))
    Ω X hX hP z hz

end Anisotropic

#print axioms Anisotropic.rough_bound
#print axioms Anisotropic.im_ent_G_mul_mono
#print axioms Anisotropic.im_mFun_div_anti
#print axioms Anisotropic.Psi_anti
#print axioms Anisotropic.cor_rough_bound'
