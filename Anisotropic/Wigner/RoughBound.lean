module

public import Anisotropic.Comparison.Ladder
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.LinAlg.Basic
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.Props
public import Anisotropic.Wigner.SelfConsistentII

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Lemma 12.6: the a priori bound -/

/-! ## The Poisson kernel `y / (t² + y²)` and the dyadic windows -/

/-- The kernel `y / (t² + y²) = Im (t − iy)⁻¹`. -/
private def rbwKer (t y : ℝ) : ℝ := y / (t ^ 2 + y ^ 2)

private lemma rbwKer_nonneg (t : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ rbwKer t y :=
  div_nonneg hy (by positivity)

/-- `y ↦ y · y / (t² + y²)` is nondecreasing on `(0, ∞)`. -/
private lemma rbwKer_mul_mono (t : ℝ) {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h : y₁ ≤ y₂) :
    y₁ * rbwKer t y₁ ≤ y₂ * rbwKer t y₂ := by
  have h₂ : 0 < y₂ := h₁.trans_le h
  unfold rbwKer
  rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hyy : y₁ * y₁ ≤ y₂ * y₂ := mul_le_mul h h h₁.le h₂.le
  nlinarith [mul_le_mul_of_nonneg_right hyy (sq_nonneg t)]

/-- `k(t, a) ≤ (b / a) k(t, b)` for `0 < a ≤ b`. -/
private lemma rbwKer_le_ratio (t : ℝ) {a b : ℝ} (ha : 0 < a) (h : a ≤ b) :
    rbwKer t a ≤ b / a * rbwKer t b := by
  have := rbwKer_mul_mono t ha h
  rw [div_mul_eq_mul_div, le_div_iff₀ ha]
  linarith

/-- `Im (x − z)⁻¹ = k(x − Re z, Im z)`. -/
private lemma rbw_inv_im (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).im = rbwKer (x - z.re) z.im := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  unfold rbwKer
  ring

/-- `|(x − z)⁻¹| = ((x − Re z)² + (Im z)²)^{−1/2}`. -/
private lemma rbw_inv_norm (x : ℝ) (z : ℂ) :
    ‖((x : ℂ) - z)⁻¹‖ = (√((x - z.re) ^ 2 + z.im ^ 2))⁻¹ := by
  rw [norm_inv, Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
    neg_sq]

/-- `|t|⁻¹ ≤ 2 b / (t² + a²)` when `0 < a ≤ |t| < b`. -/
private lemma rbw_window (t : ℝ) {a b : ℝ} (ha : 0 < a) (hat : a ≤ |t|) (htb : |t| < b) :
    |t|⁻¹ ≤ 2 * (b / a) * rbwKer t a := by
  have ht : 0 < |t| := ha.trans_le hat
  have e : 2 * (b / a) * rbwKer t a = 2 * b / (t ^ 2 + a ^ 2) := by
    unfold rbwKer
    field_simp
  rw [e, inv_eq_one_div, div_le_div_iff₀ ht (by positivity)]
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  nlinarith [mul_le_mul hat hat ha.le ht.le]

/-- One eigenvalue with `|λ − E| ≤ T` and `Im z < 1`: `|λ − z|⁻¹` is bounded by the sum of the
kernels over the ladder `η_1, …, η_L` (§12.2, proof of Lemma 12.6). -/
private lemma rbw_ladder_term {N : ℕ} (hN : 1 < N) {δ η t T : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hη1 : η < 1) (htT : |t| ≤ T) :
    (√(t ^ 2 + η ^ 2))⁻¹ ≤ (6 * (N : ℝ) ^ (2 * δ) + 2 * T) *
      ∑ l ∈ Finset.Icc 1 (ladderL N δ η), rbwKer t (ladderEta N δ η l) := by
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
  have hker : ∀ l, 0 ≤ rbwKer t (e l) := fun l => rbwKer_nonneg t (hpos l).le
  suffices hj : ∃ j ∈ Finset.Icc 1 L, (√(t ^ 2 + η ^ 2))⁻¹ ≤ C * rbwKer t (e j) by
    obtain ⟨j, hj, hle⟩ := hj
    exact hle.trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun l _ => hker l) hj) (by positivity))
  have hr : 0 < √(t ^ 2 + η ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hrt : |t| ≤ √(t ^ 2 + η ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hrη : η ≤ √(t ^ 2 + η ^ 2) :=
    calc η = √(η ^ 2) := (Real.sqrt_sq hη.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have h01 : rbwKer t η ≤ (N : ℝ) ^ δ * rbwKer t (e 1) := by
    have h1 := hsucc 0 (by omega)
    rw [he0] at h1
    have hr1 := rbwKer_le_ratio t hη (he0 ▸ (hb 0).2.2 : η ≤ e 1)
    refine hr1.trans (mul_le_mul_of_nonneg_right ?_ (hker 1))
    rw [div_le_iff₀ hη]; exact h1
  rcases lt_or_ge |t| η with hA | hA
  · refine ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hL⟩, ?_⟩
    have h1 : (√(t ^ 2 + η ^ 2))⁻¹ ≤ 2 * rbwKer t η := by
      unfold rbwKer
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hr (by positivity)]
      have : t ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      nlinarith
    calc _ ≤ 2 * rbwKer t η := h1
      _ ≤ 2 * ((N : ℝ) ^ δ * rbwKer t (e 1)) := by linarith
      _ ≤ C * rbwKer t (e 1) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by rw [hC]; nlinarith) (hker 1)
  have hinv : (√(t ^ 2 + η ^ 2))⁻¹ ≤ |t|⁻¹ :=
    inv_anti₀ (hη.trans_le hA) hrt
  rcases lt_or_ge |t| 1 with hB | hB
  · have hex : ∃ l, |t| < e l := ⟨L, by rw [heL]; exact hB⟩
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
    have hw := rbw_window t (hpos k) hkt (hk ▸ hl₀t)
    have hratio : e (k + 1) / e k ≤ (N : ℝ) ^ δ := by
      rw [div_le_iff₀ (hpos k)]; exact hsucc k (by omega)
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      refine ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hL⟩, ?_⟩
      rw [he0] at hw hratio
      calc _ ≤ |t|⁻¹ := hinv
        _ ≤ 2 * (e (0 + 1) / η) * rbwKer t η := hw
        _ ≤ 2 * (N : ℝ) ^ δ * ((N : ℝ) ^ δ * rbwKer t (e 1)) := by
            refine mul_le_mul (by linarith) h01 (rbwKer_nonneg t hη.le) (by positivity)
        _ ≤ C * rbwKer t (e 1) := by
            rw [← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (hker 1)
            rw [hC, mul_assoc, ← hN2]; nlinarith
    · refine ⟨k, Finset.mem_Icc.2 ⟨hk0, by omega⟩, ?_⟩
      calc _ ≤ |t|⁻¹ := hinv
        _ ≤ 2 * (e (k + 1) / e k) * rbwKer t (e k) := hw
        _ ≤ C * rbwKer t (e k) := by
            refine mul_le_mul_of_nonneg_right ?_ (hker k)
            rw [hC]; nlinarith
  · refine ⟨L, Finset.mem_Icc.2 ⟨hL, le_rfl⟩, ?_⟩
    have ht : 0 < |t| := one_pos.trans_le hB
    have h2 : |t|⁻¹ ≤ 2 * |t| * rbwKer t 1 := by
      unfold rbwKer
      rw [inv_eq_one_div, mul_div_assoc', mul_one, div_le_div_iff₀ ht (by positivity)]
      have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      nlinarith
    calc _ ≤ |t|⁻¹ := hinv
      _ ≤ 2 * |t| * rbwKer t 1 := h2
      _ ≤ C * rbwKer t (e L) := by
          rw [heL]
          refine mul_le_mul_of_nonneg_right ?_ (rbwKer_nonneg t zero_le_one)
          rw [hC]; nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ N by linarith) (2 * δ)]

/-- One eigenvalue, any `λ` and any `Im z > 0`: eigenvalues with `|λ − E| ≥ 1` (or `Im z ≥ 1`)
contribute at most `1`, the others are bounded by the ladder sum (§12.2, proof of Lemma 12.6). -/
private lemma rbw_term {N : ℕ} (hN : 1 < N) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (t : ℝ) :
    (√(t ^ 2 + η ^ 2))⁻¹ ≤ 1 + (6 * (N : ℝ) ^ (2 * δ) + 2) *
      ∑ l ∈ Finset.Icc 1 (ladderL N δ η), rbwKer t (ladderEta N δ η l) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ l ∈ Finset.Icc 1 (ladderL N δ η), rbwKer t (ladderEta N δ η l) := by
    refine Finset.sum_nonneg fun l _ => rbwKer_nonneg t ?_
    unfold ladderEta
    split_ifs
    · positivity
    · exact zero_le_one
  have hc : 0 ≤ 6 * (N : ℝ) ^ (2 * δ) + 2 := by positivity
  by_cases hsmall : |t| < 1 ∧ η < 1
  · have h := rbw_ladder_term hN hδ hη hsmall.2 hsmall.1.le (T := 1)
    rw [mul_one] at h
    linarith
  · have h1 : 1 ≤ √(t ^ 2 + η ^ 2) := by
      rw [Real.le_sqrt (by norm_num) (by positivity), one_pow]
      rcases not_and_or.1 hsmall with h | h
      · rw [not_lt] at h
        nlinarith [sq_abs t, abs_nonneg t]
      · rw [not_lt] at h
        nlinarith [sq_nonneg t]
    have : (√(t ^ 2 + η ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    nlinarith [mul_nonneg hc hsum]


/-! ## The spectral form of `G^W` -/

/-- A real symmetric `M` is `U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma rbw_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
    ∃ (U : Matrix (Fin N) (Fin N) ℝ) (l : Fin N → ℝ), U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      M = U * diagonal l * Uᵀ := by
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), hM.eigenvalues, ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- For `M = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ − w ≠ 0`, `(M − w)⁻¹` is the rotated
diagonal `(λₖ − w)⁻¹`. -/
private lemma rbw_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hMU : M = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ := by
    have h1 : cplx M = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hMU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (l k : ℂ) - w) =
        diagonal (fun k => (l k : ℂ)) - w • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  refine Matrix.inv_eq_right_inv ?_
  rw [hM]
  calc cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ *
        (cplx U * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ)
      = cplx U * diagonal (fun k => (l k : ℂ) - w) * ((cplx U)ᵀ * cplx U) *
        diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP', Matrix.mul_one, Matrix.mul_assoc (cplx U), Matrix.diagonal_mul_diagonal]
        have : (fun k => ((l k : ℂ) - w) * ((l k : ℂ) - w)⁻¹) = fun _ => 1 := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one, hP]

/-- A real matrix `Q` with `Qᵀ Q = 1` preserves the Euclidean norm of a test vector. -/
private lemma rbw_testNorm_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- The sandwich `⟨v, U D Uᵀ w⟩ = ∑ₖ dₖ (Uᵀ v)ₖ (Uᵀ w)ₖ`. -/
private lemma rbw_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
    (v w : Fin N → ℝ) :
    ent (cplx U * diagonal d * (cplx U)ᵀ) v w =
      ∑ k, d k * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ) := by
  have h1 : cvec v ᵥ* cplx U = cvec (Uᵀ *ᵥ v) := by
    funext k
    simp [cvec, cplx, vecMul, dotProduct, mulVec, mul_comm]
  have h2 : (cplx U)ᵀ *ᵥ cvec w = cvec (Uᵀ *ᵥ w) := by
    funext k
    simp [cvec, cplx, dotProduct, mulVec]
  unfold ent
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1,
    ← Matrix.mulVec_mulVec, h2]
  simp only [dotProduct, cvec, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- The spectral form of `G^W(z) = (W + A − z)⁻¹` for real symmetric `W + A`: an orthogonal `U`
and eigenvalues `λ` with `G_{vw}(z) = ∑ₖ (λₖ − z)⁻¹ (Uᵀv)ₖ (Uᵀw)ₖ` for all `Im z > 0`. -/
private lemma rbw_spectral {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) : ∃ (U : Matrix (Fin N) (Fin N) ℝ) (l : Fin N → ℝ),
      (∀ v : Fin N → ℝ, ∑ k, (Uᵀ *ᵥ v) k ^ 2 = testNorm v ^ 2) ∧
      ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (GW A Wm z) v w =
        ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ) := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := rbw_eig_decomp (hW'.add hA)
  refine ⟨U, l, fun v => ?_, fun z hz v w => ?_⟩
  · rw [← rbw_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v]
    unfold testNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  · have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
      rbw_resolvent_eq hUU hUU' hMU hne
    rw [hG, rbw_ent_sandwich]

section Spectral

variable {N : ℕ} {G : ℂ → Matrix (Fin N) (Fin N) ℂ} {U : Matrix (Fin N) (Fin N) ℝ}
  {l : Fin N → ℝ}

/-- `Im G_{vv}(z) = ∑ₖ (Uᵀv)ₖ² k(λₖ − E, η)`. -/
private lemma rbw_im_eq (hG : ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (G z) v w =
      ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ))
    {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) :
    (ent (G z) v v).im = ∑ k, (Uᵀ *ᵥ v) k ^ 2 * rbwKer (l k - z.re) z.im := by
  rw [hG z hz, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.im_mul_ofReal, rbw_inv_im]
  ring

/-- `|G_{vw}(z)| ≤ ∑ₖ |(Uᵀv)ₖ| |(Uᵀw)ₖ| |λₖ − z|⁻¹`. -/
private lemma rbw_norm_le (hG : ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (G z) v w =
      ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ))
    {z : ℂ} (hz : 0 < z.im) (v w : Fin N → ℝ) :
    ‖ent (G z) v w‖ ≤ ∑ k, |(Uᵀ *ᵥ v) k| * |(Uᵀ *ᵥ w) k| *
      (√((l k - z.re) ^ 2 + z.im ^ 2))⁻¹ := by
  rw [hG z hz v w]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
  rw [norm_mul, rbw_inv_norm, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  ring

/-- `η ↦ η Im G_{vv}(E + iη)` is nondecreasing. -/
private lemma rbw_im_mono (hG : ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (G z) v w =
      ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ))
    {z z' : ℂ} (hre : z'.re = z.re) (hz : 0 < z.im) (h : z.im ≤ z'.im) (v : Fin N → ℝ) :
    z.im * (ent (G z) v v).im ≤ z'.im * (ent (G z') v v).im := by
  have hz' : 0 < z'.im := hz.trans_le h
  rw [rbw_im_eq hG hz, rbw_im_eq hG hz', Finset.mul_sum, Finset.mul_sum, hre]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := mul_le_mul_of_nonneg_left (rbwKer_mul_mono (l k - z.re) hz h)
    (sq_nonneg ((Uᵀ *ᵥ v) k))
  linarith

/-- The deterministic part of Lemma 12.6 (i): if `Im G_{xx}(E + iη_j) ≤ β |x|²` on the ladder
`j = 1, …, L` for `x = v, w`, then `|G_{vw}(z)| ≤ (1 + (6N^{2δ} + 2) L β) |v| |w|`. -/
private lemma rbw_bilin_le (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ)
    (hnorm : ∀ v : Fin N → ℝ, ∑ k, (Uᵀ *ᵥ v) k ^ 2 = testNorm v ^ 2)
    (hG : ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (G z) v w =
      ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ))
    {z : ℂ} (hz : 0 < z.im) {β : ℝ} (hβ : 0 ≤ β) {v w : Fin N → ℝ}
    (hv : ∀ j ∈ Finset.Icc 1 (ladderL N δ z.im),
      (ent (G (ladderPt N δ z j)) v v).im ≤ β * testNorm v ^ 2)
    (hw : ∀ j ∈ Finset.Icc 1 (ladderL N δ z.im),
      (ent (G (ladderPt N δ z j)) w w).im ≤ β * testNorm w ^ 2) :
    ‖ent (G z) v w‖ ≤ (1 + (6 * (N : ℝ) ^ (2 * δ) + 2) * ladderL N δ z.im * β) *
      testNorm v * testNorm w := by
  set L := ladderL N δ z.im with hLdef
  set c := 6 * (N : ℝ) ^ (2 * δ) + 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set B := 1 + c * L * β with hB
  have hB0 : 0 ≤ B := by positivity
  set r : Fin N → ℝ := fun k => (√((l k - z.re) ^ 2 + z.im ^ 2))⁻¹ with hrdef
  have hr0 : ∀ k, 0 ≤ r k := fun k => inv_nonneg.2 (Real.sqrt_nonneg _)
  have hpos : ∀ j, 0 < (ladderPt N δ z j).im := by
    intro j
    show 0 < ladderEta N δ z.im j
    unfold ladderEta
    split_ifs
    · exact mul_pos hz (Real.rpow_pos_of_pos (by positivity) _)
    · exact zero_lt_one
  have key : ∀ x : Fin N → ℝ, (∀ j ∈ Finset.Icc 1 L,
      (ent (G (ladderPt N δ z j)) x x).im ≤ β * testNorm x ^ 2) →
      ∑ k, (Uᵀ *ᵥ x) k ^ 2 * r k ≤ B * testNorm x ^ 2 := by
    intro x hx
    calc ∑ k, (Uᵀ *ᵥ x) k ^ 2 * r k
        ≤ ∑ k, (Uᵀ *ᵥ x) k ^ 2 * (1 + c * ∑ j ∈ Finset.Icc 1 L,
            rbwKer (l k - z.re) (ladderEta N δ z.im j)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
            (rbw_term hN hδ hz (l k - z.re)) (sq_nonneg _)
      _ = ∑ k, (Uᵀ *ᵥ x) k ^ 2 + c * ∑ j ∈ Finset.Icc 1 L,
            ∑ k, (Uᵀ *ᵥ x) k ^ 2 * rbwKer (l k - z.re) (ladderEta N δ z.im j) := by
          rw [Finset.sum_comm (s := Finset.Icc 1 L), Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_add, mul_one]
          congr 1
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = testNorm x ^ 2 + c * ∑ j ∈ Finset.Icc 1 L,
            (ent (G (ladderPt N δ z j)) x x).im := by
          rw [hnorm]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [rbw_im_eq hG (hpos j) x]
          rfl
      _ ≤ testNorm x ^ 2 + c * ∑ j ∈ Finset.Icc 1 L, β * testNorm x ^ 2 := by
          gcongr with j hj
          exact hx j hj
      _ = B * testNorm x ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hB]
          simp only [add_tsub_cancel_right]
          ring
  have hsv := key v hv
  have hsw := key w hw
  calc ‖ent (G z) v w‖ ≤ ∑ k, |(Uᵀ *ᵥ v) k| * |(Uᵀ *ᵥ w) k| * r k := rbw_norm_le hG hz v w
    _ = ∑ k, (|(Uᵀ *ᵥ v) k| * √(r k)) * (|(Uᵀ *ᵥ w) k| * √(r k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_mul_mul_comm, Real.mul_self_sqrt (hr0 k)]
    _ ≤ √(∑ k, (|(Uᵀ *ᵥ v) k| * √(r k)) ^ 2) * √(∑ k, (|(Uᵀ *ᵥ w) k| * √(r k)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = √(∑ k, (Uᵀ *ᵥ v) k ^ 2 * r k) * √(∑ k, (Uᵀ *ᵥ w) k ^ 2 * r k) := by
        congr 2 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;>
          rw [mul_pow, sq_abs, Real.sq_sqrt (hr0 k)]
    _ ≤ √(B * testNorm v ^ 2) * √(B * testNorm w ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hsv) (Real.sqrt_le_sqrt hsw) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = B * testNorm v * testNorm w := by
        rw [Real.sqrt_mul hB0, Real.sqrt_mul hB0,
          Real.sqrt_sq (show 0 ≤ testNorm v from Real.sqrt_nonneg _),
          Real.sqrt_sq (show 0 ≤ testNorm w from Real.sqrt_nonneg _),
          show √B * testNorm v * (√B * testNorm w) = (√B * √B) * testNorm v * testNorm w by ring,
          Real.mul_self_sqrt hB0]

end Spectral


/-! ## Ladder points, `Ψ^W` and normalization -/

/-- For a spectral domain `S ⊆ 𝐃^W`, the ladder points `l ≥ 1` of `z ∈ S_m` with `Im z ≤ 1` lie
in `S_{m−1}`. -/
private lemma rbw_ladderPt_level {τ : ℝ} {N : ℕ} {S : Set ℂ} (hS : SpectralDomainW τ N S)
    (hτ1 : τ ≤ 1) (hN : 1 < N) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 1 ≤ m) {z : ℂ}
    (hz : z ∈ levelSet N δ S m) (hz1 : z.im ≤ 1) {l : ℕ} (hl : 1 ≤ l) :
    ladderPt N δ z l ∈ levelSet N δ S (m - 1) := by
  obtain ⟨h0, hre, hη, him⟩ := hS.1 hz.1
  have hτ : 0 < τ := inv_pos.1 (lt_of_lt_of_le h0 him)
  have hτinv : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  obtain ⟨hb1, hb2, -⟩ := ladderEta_bounds hN hδ h0 hz1 l
  have hre' : (ladderPt N δ z l).re = z.re := rfl
  have him' : (ladderPt N δ z l).im = ladderEta N δ z.im l := rfl
  refine ⟨hS.2 z hz.1 _ ⟨by rw [him']; linarith, by rw [hre']; exact hre,
    by rw [him']; exact hη.trans hb1, by rw [him']; exact hb2.trans hτinv⟩ hre'
    (by rw [him']; exact hb1), ?_⟩
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  rw [him', Nat.cast_sub hm, Nat.cast_one]
  unfold ladderEta
  split_ifs with h
  · have h1 : (N : ℝ) ^ δ ≤ (N : ℝ) ^ (δ * (l : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hN1.le ?_
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    have h2 : (N : ℝ) ^ (-(δ * ((m : ℝ) - 1))) = (N : ℝ) ^ (-(δ * (m : ℝ))) * (N : ℝ) ^ δ := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    have hz2 := hz.2
    have hpos : 0 < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hNp _
    have hpos2 : 0 < (N : ℝ) ^ (-(δ * (m : ℝ))) := Real.rpow_pos_of_pos hNp _
    rw [h2]
    calc (N : ℝ) ^ (-(δ * (m : ℝ))) * (N : ℝ) ^ δ ≤ z.im * (N : ℝ) ^ δ :=
          mul_le_mul_of_nonneg_right hz2 hpos.le
      _ ≤ z.im * (N : ℝ) ^ (δ * (l : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (lt_of_lt_of_le hpos2 hz2).le
  · refine Real.rpow_le_one_of_one_le_of_nonpos hN1.le ?_
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- `Ψ^W ≥ 0`, `Im m^W / (Nη) ≤ (Ψ^W)²` and `(Nη)⁻¹ ≤ Ψ^W`. -/
private lemma rbw_psi_facts {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ PsiW a z ∧ (mW a z).im / (N * z.im) ≤ PsiW a z ^ 2 ∧ 1 / (N * z.im) ≤ PsiW a z := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := (mW_spec hN a hz).1
  have hq : 0 ≤ (mW a z).im / (N * z.im) := by positivity
  have hp : 0 ≤ 1 / (N * z.im) := by positivity
  have hs := Real.sq_sqrt hq
  have hs0 := Real.sqrt_nonneg ((mW a z).im / (N * z.im))
  unfold PsiW
  refine ⟨by positivity, ?_, by linarith⟩
  nlinarith

/-- On `𝐃^W(τ, N)` with `C₀δ ≤ τ/4`: `N^{C₀δ} Ψ^W ≤ 2`. -/
private lemma rbw_psi_small {τ : ℝ} {N : ℕ} (hN : 1 ≤ N) {C₀ δ : ℝ}
    (hC₀δ : C₀ * δ ≤ τ / 4) (hC0δ : 0 ≤ C₀ * δ) (a : Fin N → ℝ) {z : ℂ} (hz : z ∈ domW τ N) :
    (N : ℝ) ^ (C₀ * δ) * PsiW a z ≤ 2 := by
  obtain ⟨h0, -, hη, -⟩ := hz
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hX : (N : ℝ) ^ τ ≤ (N : ℝ) * z.im := by
    calc (N : ℝ) ^ τ = N * (N : ℝ) ^ (-1 + τ) := by
          rw [Real.rpow_add hNpos, Real.rpow_neg_one]; field_simp
      _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hη hNpos.le
  have hXpos : 0 < (N : ℝ) * z.im := by positivity
  have hτ0 : 0 ≤ τ := by linarith
  have ha1 : 1 ≤ (N : ℝ) ^ (C₀ * δ) := Real.one_le_rpow hN1 hC0δ
  have ha2 : ((N : ℝ) ^ (C₀ * δ)) ^ 2 ≤ (N : ℝ) * z.im := by
    calc ((N : ℝ) ^ (C₀ * δ)) ^ 2 = (N : ℝ) ^ (C₀ * δ + C₀ * δ) := by
          rw [Real.rpow_add hNpos]; ring
      _ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ _ := hX
  have hm0 := (mW_spec hN a h0).1
  have hm1 : (mW a z).im < 1 :=
    (Complex.im_le_norm _).trans_lt (norm_mW_lt_one hN a h0)
  have h1 : (N : ℝ) ^ (C₀ * δ) * √((mW a z).im / (N * z.im)) ≤ 1 := by
    rw [← Real.sqrt_sq (show 0 ≤ (N : ℝ) ^ (C₀ * δ) by linarith), ← Real.sqrt_mul (sq_nonneg _)]
    refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
    rw [mul_div_assoc', div_le_one hXpos]
    nlinarith
  have h2 : (N : ℝ) ^ (C₀ * δ) * (1 / (N * z.im)) ≤ 1 := by
    rw [mul_one_div, div_le_one hXpos]
    nlinarith
  unfold PsiW
  rw [mul_add]
  linarith

/-- `|c x| = |c| |x|`. -/
private lemma rbw_testNorm_smul {N : ℕ} (c : ℝ) (x : Fin N → ℝ) :
    testNorm (c • x) = |c| * testNorm x := by
  unfold testNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- `x = |x| · (|x|⁻¹ x)`. -/
private lemma rbw_testNorm_smul_self {N : ℕ} (x : Fin N → ℝ) :
    testNorm x • ((testNorm x)⁻¹ • x) = x := by
  by_cases h : testNorm x = 0
  · have hx : x = 0 := by
      unfold testNorm at h
      rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
      funext s
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h s
        (Finset.mem_univ _)
      simpa using this
    simp [hx]
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- `G_{cx, cx} = c² G_{xx}`. -/
private lemma rbw_ent_smul {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (y : Fin N → ℝ) :
    ent G (c • y) (c • y) = ((c ^ 2 : ℝ) : ℂ) * ent G y y := by
  have hc : cvec (c • y) = (c : ℂ) • cvec y := by
    funext s
    simp [cvec]
  unfold ent
  rw [hc, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  push_cast
  ring


/-- The arithmetic of Lemma 12.6 (ii): from `η g ≤ η' g'`, `g' ≤ p(μ' + cΨ')`, `μ'/(nη') ≤ Ψ'²`,
`0 ≤ Ψ' ≤ Ψ`, `(nη)⁻¹ ≤ Ψ`, `η' ≤ sη`, `p ≥ 2`, `s² ≤ T = sc`, conclude `g/(nη) ≤ p² T Ψ²`. -/
private lemma rbw_arith {g g' μ' Ψ Ψ' η η' n pε s c T : ℝ} (hn : 0 < n) (hz0 : 0 < η)
    (hmono : η * g ≤ η' * g') (hc : g' ≤ pε * (μ' + c * Ψ')) (hP1' : μ' / (n * η') ≤ Ψ' ^ 2)
    (hP0' : 0 ≤ Ψ') (hanti : Ψ' ≤ Ψ) (hP2 : 1 / (n * η) ≤ Ψ) (hle : η ≤ η') (hge : η' ≤ s * η)
    (hpε : 2 ≤ pε) (hs0 : 0 ≤ s) (hc0 : 0 ≤ c) (hss : s * s ≤ T) (hsc : s * c = T) :
    g / (n * η) ≤ pε * pε * (T * Ψ ^ 2) := by
  have hP0 : 0 ≤ Ψ := hP0'.trans hanti
  have hNη : 0 < n * η := by positivity
  have hz'0 : 0 < η' := hz0.trans_le hle
  set r := η' / η with hr
  have hr0 : 0 ≤ r := by positivity
  have hrs : r ≤ s := by rw [hr, div_le_iff₀ hz0]; exact hge
  have ha1 : g / (n * η) ≤ r * (g' / (n * η)) := by
    rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hNη.le
    rw [hr, div_mul_eq_mul_div, le_div_iff₀ hz0]
    linarith
  have ha2 : g' / (n * η) ≤ pε * (μ' / (n * η) + c * (Ψ' * (1 / (n * η)))) := by
    have : g' / (n * η) ≤ pε * (μ' + c * Ψ') / (n * η) :=
      div_le_div_of_nonneg_right hc hNη.le
    refine this.trans (le_of_eq ?_)
    field_simp
  have ha3 : μ' / (n * η) ≤ s * Ψ ^ 2 := by
    have e : μ' / (n * η) = r * (μ' / (n * η')) := by
      rw [hr]; field_simp
    rw [e]
    have hΨ2 : Ψ' ^ 2 ≤ Ψ ^ 2 := pow_le_pow_left₀ hP0' hanti 2
    calc r * (μ' / (n * η')) ≤ r * Ψ' ^ 2 := mul_le_mul_of_nonneg_left hP1' hr0
      _ ≤ s * Ψ ^ 2 := mul_le_mul hrs hΨ2 (sq_nonneg _) hs0
  have ha4 : c * (Ψ' * (1 / (n * η))) ≤ c * Ψ ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hc0
    rw [sq]
    exact mul_le_mul hanti hP2 (by positivity) hP0
  have hΨ0 : 0 ≤ Ψ ^ 2 := sq_nonneg _
  have hpε0 : 0 ≤ pε := by linarith
  have hin : μ' / (n * η) + c * (Ψ' * (1 / (n * η))) ≤ s * Ψ ^ 2 + c * Ψ ^ 2 := by linarith
  have hb1 : g' / (n * η) ≤ pε * (s * Ψ ^ 2 + c * Ψ ^ 2) :=
    ha2.trans (mul_le_mul_of_nonneg_left hin hpε0)
  have hb2 : g / (n * η) ≤ s * (pε * (s * Ψ ^ 2 + c * Ψ ^ 2)) := by
    refine ha1.trans ?_
    have hnn : 0 ≤ pε * (s * Ψ ^ 2 + c * Ψ ^ 2) := by positivity
    rcases le_total 0 (g' / (n * η)) with h0 | h0
    · exact mul_le_mul hrs hb1 h0 hs0
    · nlinarith
  have hb3 : s * (pε * (s * Ψ ^ 2 + c * Ψ ^ 2)) = pε * ((s * s + s * c) * Ψ ^ 2) := by ring
  rw [hb3] at hb2
  have hb4 : (s * s + s * c) * Ψ ^ 2 ≤ 2 * T * Ψ ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ hΨ0
    linarith
  have hT0 : 0 ≤ T * Ψ ^ 2 := mul_nonneg ((mul_nonneg hs0 hs0).trans hss) hΨ0
  calc g / (n * η) ≤ pε * ((s * s + s * c) * Ψ ^ 2) := hb2
    _ ≤ pε * (2 * T * Ψ ^ 2) := mul_le_mul_of_nonneg_left hb4 hpε0
    _ = 2 * (pε * (T * Ψ ^ 2)) := by ring
    _ ≤ pε * (pε * (T * Ψ ^ 2)) := mul_le_mul_of_nonneg_right hpε (by positivity)
    _ = pε * pε * (T * Ψ ^ 2) := by ring

/-! ## Lemma 12.6 -/
set_option maxHeartbeats 1000000 in

/-- Lemma 12.6 (a priori bounds, (a_priori_wig)) from (A_{m−1}). -/
theorem wig_rough_bound (τ : ℝ) (C : ℕ → ℝ) (C₀ δ εA DA : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hεA : 0 < εA) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (P : ModelClassW N)
      (m : ℕ), WigSetting τ N A S → 1 ≤ m → PropAW N C P A S C₀ δ (m - 1) εA DA →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
        ∀ z ∈ levelSet N δ S m,
          (∀ v w : Fin N → ℝ, DomAt N (2 * εA) (DA - 1)
            (fun ω => ‖testBilin v (GW A (W ω) z - piW A z) w‖)
            (fun _ => (N : ℝ) ^ (2 * δ) * testNorm v * testNorm w)) ∧
          (∀ v : Fin N → ℝ, testNorm v = 1 → DomAt N (2 * εA) DA
            (fun ω => (ent (GW A (W ω) z) v v).im / (N * z.im))
            (fun _ => (N : ℝ) ^ ((C₀ + 1) * δ) * PsiW (specOf A) z ^ 2)) := by
  set K : ℝ := 1 + τ⁻¹ + 24 * (δ⁻¹ + 1) with hK
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  have hK0 : 0 < K := by positivity
  have hK2 : 2 ≤ K := by linarith
  refine ⟨max (⌈2 * (δ⁻¹ + 1)⌉₊ + 2) ⌈K ^ εA⁻¹⌉₊, ?_⟩
  intro N hN A S P m hset hm hA Ω _ _ W hW hP z hz
  have hN2 : 2 ≤ N := le_trans (by omega) (le_trans (le_max_left _ _) hN)
  have hN1 : 1 < N := hN2
  have hN1' : 1 ≤ N := hN1.le
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hNL : 2 * (δ⁻¹ + 1) ≤ (N : ℝ) := by
    have h0 : ⌈2 * (δ⁻¹ + 1)⌉₊ + 2 ≤ N := le_trans (le_max_left _ _) hN
    have h1 : (⌈2 * (δ⁻¹ + 1)⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈2 * (δ⁻¹ + 1)⌉₊ ≤ N)
    exact (Nat.le_ceil _).trans h1
  have hNε : K ≤ (N : ℝ) ^ εA := by
    have h0 : ⌈K ^ εA⁻¹⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    have h1 : K ^ εA⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h0)
    calc K = (K ^ εA⁻¹) ^ εA := (Real.rpow_inv_rpow hK0.le hεA.ne').symm
      _ ≤ (N : ℝ) ^ εA := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le _) h1 hεA.le
  have hp2 : (N : ℝ) ^ (2 * εA) = (N : ℝ) ^ εA * (N : ℝ) ^ εA := by
    rw [two_mul, Real.rpow_add hNpos]
  have hC0δ : 0 ≤ C₀ * δ := by nlinarith
  obtain ⟨hzS, hzlev⟩ := hz
  obtain ⟨hz0, hzE, hzη, hzτ⟩ := hset.domain.1 hzS
  set a := specOf A with ha
  have hηN : (N : ℝ) ^ (-1 : ℝ) ≤ z.im :=
    (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)).trans hzη
  have hL : (ladderL N δ z.im : ℝ) ≤ δ⁻¹ + 1 := ladderL_le hN1 hδ hηN
  have hlad : ∀ j ∈ Finset.Icc 1 (ladderL N δ z.im),
      ladderPt N δ z j ∈ levelSet N δ S (m - 1) := by
    intro j hj
    obtain ⟨hj1, hjL⟩ := Finset.mem_Icc.1 hj
    have hη1 : z.im < 1 := by
      have h0 : 0 < ladderL N δ z.im := by omega
      rw [ladderL, Nat.ceil_pos] at h0
      have hlog : 0 < Real.log z.im⁻¹ := by
        by_contra hc
        push Not at hc
        have := div_nonpos_of_nonpos_of_nonneg hc
          (mul_nonneg hδ.le (Real.log_nonneg hNone))
        linarith
      rw [Real.log_inv, neg_pos] at hlog
      exact (Real.log_neg_iff hz0).1 hlog
    exact rbw_ladderPt_level hset.domain hset.le_one hN1 hδ hm ⟨hzS, hzlev⟩ hη1.le hj1
  refine ⟨fun v w => ?_, fun v hv => ?_⟩
  · -- (i): the ladder and (A_{m−1}) at the ladder points
    set L := ladderL N δ z.im with hLdef
    set ψ : ℕ → ℝ := fun j => (mW a (ladderPt N δ z j)).im +
      (N : ℝ) ^ (C₀ * δ) * PsiW a (ladderPt N δ z j) with hψdef
    have hψ : ∀ j ∈ Finset.Icc 1 L, 0 ≤ ψ j ∧ ψ j ≤ 3 := by
      intro j hj
      have hD := hset.domain.1 (hlad j hj).1
      have him := hD.1
      have hm0 := (mW_spec hN1' a him).1
      have hm1 : (mW a (ladderPt N δ z j)).im < 1 :=
        (Complex.im_le_norm _).trans_lt (norm_mW_lt_one hN1' a him)
      have hps := rbw_psi_small hN1' hC₀δ hC0δ a hD
      have hps0 := (rbw_psi_facts hN1' a him).1
      have : 0 ≤ (N : ℝ) ^ (C₀ * δ) * PsiW a (ladderPt N δ z j) :=
        mul_nonneg (Real.rpow_nonneg hNpos.le _) hps0
      constructor <;> simp only [hψdef] <;> linarith
    set u : (Fin N → ℝ) → (Fin N → ℝ) := fun x => (testNorm x)⁻¹ • x with hudef
    set B : (Fin N → ℝ) → Set Ω := fun x => ⋃ j ∈ Finset.Icc 1 L,
      {ω | (N : ℝ) ^ εA * ψ j < (ent (GW A (W ω) (ladderPt N δ z j)) (u x) (u x)).im}
      with hBdef
    have hBprob : ∀ x, ℙ (B x) ≤ (L : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ (-DA)) := by
      intro x
      refine (measure_biUnion_finset_le _ _).trans ?_
      calc ∑ j ∈ Finset.Icc 1 L, ℙ {ω | (N : ℝ) ^ εA * ψ j <
            (ent (GW A (W ω) (ladderPt N δ z j)) (u x) (u x)).im}
          ≤ ∑ j ∈ Finset.Icc 1 L, ENNReal.ofReal ((N : ℝ) ^ (-DA)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            by_cases h0 : testNorm x = 0
            · have hu0 : u x = 0 := by simp [hudef, h0]
              have hempty : {ω | (N : ℝ) ^ εA * ψ j <
                  (ent (GW A (W ω) (ladderPt N δ z j)) (u x) (u x)).im} = ∅ := by
                ext ω
                simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hu0]
                have : ent (GW A (W ω) (ladderPt N δ z j)) 0 0 = 0 := by
                  have h0 : cvec (0 : Fin N → ℝ) = 0 := by
                    funext s
                    simp [cvec]
                  unfold ent
                  rw [h0, Matrix.mulVec_zero, dotProduct_zero]
                rw [this, Complex.zero_im]
                exact mul_nonneg (Real.rpow_nonneg hNpos.le _) (hψ j hj).1
              rw [hempty, measure_empty]
              exact zero_le
            · have hu : testNorm (u x) = 1 := by
                rw [hudef, rbw_testNorm_smul, abs_inv,
                  abs_of_nonneg (show (0 : ℝ) ≤ testNorm x from Real.sqrt_nonneg _)]
                exact inv_mul_cancel₀ h0
              exact hA Ω W hW hP _ (hlad j hj) (u x) hu
        _ = (L : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ (-DA)) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, add_tsub_cancel_right]
    have hBgood : ∀ x ω, ω ∉ B x → ∀ j ∈ Finset.Icc 1 L,
        (ent (GW A (W ω) (ladderPt N δ z j)) x x).im ≤
          3 * (N : ℝ) ^ εA * testNorm x ^ 2 := by
      intro x ω hω j hj
      have hω' : (ent (GW A (W ω) (ladderPt N δ z j)) (u x) (u x)).im ≤ (N : ℝ) ^ εA * ψ j := by
        by_contra hc
        push Not at hc
        exact hω (Set.mem_biUnion hj hc)
      have hsc := rbw_ent_smul (GW A (W ω) (ladderPt N δ z j)) (testNorm x) (u x)
      rw [hudef, rbw_testNorm_smul_self] at hsc
      rw [hsc, Complex.im_ofReal_mul]
      have hNε0 : 0 ≤ (N : ℝ) ^ εA := Real.rpow_nonneg hNpos.le _
      calc testNorm x ^ 2 * (ent (GW A (W ω) (ladderPt N δ z j)) (u x) (u x)).im
          ≤ testNorm x ^ 2 * ((N : ℝ) ^ εA * ψ j) :=
            mul_le_mul_of_nonneg_left hω' (sq_nonneg _)
        _ ≤ testNorm x ^ 2 * ((N : ℝ) ^ εA * 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hψ j hj).2 hNε0)
              (sq_nonneg _)
        _ = 3 * (N : ℝ) ^ εA * testNorm x ^ 2 := by ring
    have hnum : 1 + (6 * (N : ℝ) ^ (2 * δ) + 2) * L * (3 * (N : ℝ) ^ εA) + τ⁻¹ ≤
        (N : ℝ) ^ (2 * εA) * (N : ℝ) ^ (2 * δ) := by
      have hp1 : 1 ≤ (N : ℝ) ^ (2 * δ) := Real.one_le_rpow hNone (by linarith)
      have hq1 : 1 ≤ (N : ℝ) ^ εA := le_trans (by linarith) hNε
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      set p := (N : ℝ) ^ (2 * δ)
      set q := (N : ℝ) ^ εA
      rw [hp2]
      have h1 : (6 * p + 2) * L * (3 * q) ≤ 24 * L * p * q := by
        have : 6 * p + 2 ≤ 8 * p := by linarith
        have hLq : 0 ≤ (L : ℝ) * (3 * q) := by positivity
        nlinarith
      have h2 : 1 + τ⁻¹ ≤ (1 + τ⁻¹) * (p * q) := by
        have : 1 ≤ p * q := by nlinarith
        nlinarith
      have h3 : (1 + τ⁻¹ + 24 * L) * (p * q) ≤ K * (p * q) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hK]
        linarith
      have h4 : K * (p * q) ≤ q * (p * q) :=
        mul_le_mul_of_nonneg_right hNε (by positivity)
      nlinarith
    have hsub : {ω | (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm v * testNorm w) <
        ‖testBilin v (GW A (W ω) z - piW A z) w‖} ⊆ B v ∪ B w := by
      intro ω hω
      by_contra hc
      rw [Set.mem_union, not_or] at hc
      have hgv := hBgood v ω hc.1
      have hgw := hBgood w ω hc.2
      obtain ⟨U, l, hnorm, hG⟩ := rbw_spectral hset.symmA (hW.symm ω)
      have hb := rbw_bilin_le hN1 hδ hnorm hG hz0
        (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ) ^ εA) hgv hgw
      have hpi := norm_piW_le hset.pos hset.symmA hset.standing hzS v w
      have hsplit : testBilin v (GW A (W ω) z - piW A z) w =
          ent (GW A (W ω) z) v w - testBilin v (piW A z) w := by
        simp only [testBilin, ent, Matrix.sub_mulVec, dotProduct_sub]
      simp only [Set.mem_ofPred_eq] at hω
      rw [hsplit] at hω
      have htri := norm_sub_le (ent (GW A (W ω) z) v w) (testBilin v (piW A z) w)
      have hv0 : 0 ≤ testNorm v := Real.sqrt_nonneg _
      have hw0 : 0 ≤ testNorm w := Real.sqrt_nonneg _
      have hvw : 0 ≤ testNorm v * testNorm w := mul_nonneg hv0 hw0
      have := mul_le_mul_of_nonneg_right hnum hvw
      nlinarith
    unfold DomAt
    calc ℙ {ω | (N : ℝ) ^ (2 * εA) * ((N : ℝ) ^ (2 * δ) * testNorm v * testNorm w) <
          ‖testBilin v (GW A (W ω) z - piW A z) w‖}
        ≤ ℙ (B v ∪ B w) := measure_mono hsub
      _ ≤ ℙ (B v) + ℙ (B w) := measure_union_le _ _
      _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ (-DA)) +
          (L : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) ^ (-DA)) := add_le_add (hBprob v) (hBprob w)
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(DA - 1))) := by
          rw [← add_mul, ← Nat.cast_add, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          rw [show -(DA - 1) = -DA + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
          have hLL : ((L + L : ℕ) : ℝ) ≤ N := by push_cast; linarith
          nlinarith [Real.rpow_nonneg hNpos.le (-DA)]
  · -- (ii): one ladder step and (A_{m−1}) at that point
    have hex : ∃ z' : ℂ, z' ∈ levelSet N δ S (m - 1) ∧ z'.re = z.re ∧ z.im ≤ z'.im ∧
        z'.im ≤ (N : ℝ) ^ δ * z.im := by
      by_cases hη1 : z.im < 1
      · have hηNδ : z.im < (N : ℝ) ^ δ := hη1.trans (Real.one_lt_rpow (by linarith) hδ)
        have hL0 : 0 < ladderL N δ z.im :=
          (ladderL_spec hN1 hδ hz0 hηNδ).2 1 (by simpa using hη1)
        refine ⟨ladderPt N δ z 1, rbw_ladderPt_level hset.domain hset.le_one hN1 hδ hm
          ⟨hzS, hzlev⟩ hη1.le le_rfl, rfl, (ladderEta_bounds hN1 hδ hz0 hη1.le 1).1, ?_⟩
        have h := ladderEta_succ_le hN1 hδ hz0 hηNδ hL0
        have he0 : ladderEta N δ z.im 0 = z.im := by simp [ladderEta, hL0]
        rw [he0] at h
        exact h
      · refine ⟨z, ⟨hzS, ?_⟩, rfl, le_rfl, ?_⟩
        · have hm0 : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          exact (Real.rpow_le_one_of_one_le_of_nonpos hNone (by nlinarith)).trans
            (not_lt.1 hη1)
        · exact le_mul_of_one_le_left hz0.le (Real.one_le_rpow hNone hδ.le)
    obtain ⟨z', hz'lev, hre, hle, hge⟩ := hex
    have hz'0 : 0 < z'.im := hz0.trans_le hle
    have hev := hA Ω W hW hP z' hz'lev v hv
    unfold DomAt at hev ⊢
    refine le_trans (measure_mono ?_) hev
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hc
    push Not at hc
    obtain ⟨U, l, -, hG⟩ := rbw_spectral hset.symmA (hW.symm ω)
    have hmono := rbw_im_mono hG hre hz0 hle v
    obtain ⟨hP0, -, hP2⟩ := rbw_psi_facts hN1' a hz0
    obtain ⟨hP0', hP1', -⟩ := rbw_psi_facts hN1' a hz'0
    have hanti : PsiW a z' ≤ PsiW a z := by
      have h := PsiW_anti hN1' a z.re hz0 hle
      have e1 : (⟨z.re, z'.im⟩ : ℂ) = z' := Complex.ext hre.symm rfl
      have e2 : (⟨z.re, z.im⟩ : ℂ) = z := Complex.ext rfl rfl
      rwa [e1, e2] at h
    have hpε : 2 ≤ (N : ℝ) ^ εA := hK2.trans hNε
    have hss : (N : ℝ) ^ δ * (N : ℝ) ^ δ ≤ (N : ℝ) ^ ((C₀ + 1) * δ) := by
      have h1 : 1 * δ ≤ C₀ * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      rw [← Real.rpow_add hNpos]
      refine Real.rpow_le_rpow_of_exponent_le hNone ?_
      rw [add_mul, one_mul]
      linarith
    have hsc : (N : ℝ) ^ δ * (N : ℝ) ^ (C₀ * δ) = (N : ℝ) ^ ((C₀ + 1) * δ) := by
      rw [← Real.rpow_add hNpos, add_mul, one_mul, add_comm (C₀ * δ) δ]
    have hfin := rbw_arith hNpos hz0 hmono hc hP1' hP0' hanti hP2 hle hge hpε
      (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _) hss hsc
    rw [hp2] at hω
    exact lt_irrefl _ (hω.trans_le hfin)


#print axioms wig_rough_bound

end Anisotropic
