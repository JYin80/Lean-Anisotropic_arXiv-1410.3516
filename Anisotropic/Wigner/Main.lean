import Anisotropic.Comparison.MainII
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Comparison
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.GaussDiag
import Anisotropic.Wigner.GaussRotate
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Theorem 12.2 (i): the anisotropic law for `W + A` (class, literal and TeX forms) -/

/-! ## Elementary tools: spectral form of `Π^W`, monotonicity, polarization -/

/-- For `M = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ − w ≠ 0`, the rotated diagonal
`(λₖ − w)⁻¹` is a right inverse of `M − w`. -/
private lemma wmain_right_inv {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hMU : M = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      ((cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ) = 1 := by
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

private lemma wmain_ent_sub {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X - Y) x y = ent X x y - ent Y x y := by
  simp [ent, Matrix.sub_mulVec, dotProduct_sub]

private lemma wmain_testNorm_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

private lemma wmain_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
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

private lemma wmain_psi_pos {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < PsiW a z := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  unfold PsiW
  have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  linarith [Real.sqrt_nonneg ((mW a z).im / (N * z.im))]

/-- Monotonicity of `DomAt` in `ε` and `D`. -/
private lemma wmain_domAt_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N) {ε ε' D D' : ℝ}
    {ξ ζ : Ω → ℝ} (hζ : ∀ ω, 0 ≤ ζ ω) (hε : ε ≤ ε') (hD : D' ≤ D) (h : DomAt N ε D ξ ζ) :
    DomAt N ε' D' ξ ζ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold DomAt at h ⊢
  refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 hε) (hζ ω)) hω

private lemma wmain_mW_im_nonneg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (mW a z).im := (mW_spec hN a hz).1.le

/-- Monotonicity of (A_m) in `ε` and `D`. -/
private lemma wmain_propA_mono {N : ℕ} {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    {P : ModelClassW N} {C : ℕ → ℝ} {C₀ δ ε ε' D D' : ℝ} {m : ℕ} (hset : WigSetting τ N A S)
    (hN : 1 ≤ N) (hε : ε ≤ ε') (hD : D' ≤ D) (h : PropAW N C P A S C₀ δ m ε D) :
    PropAW N C P A S C₀ δ m ε' D' := by
  intro Ω _ _ W hW hP z hz v hv
  have hzim : 0 < z.im := (hset.domain.1 hz.1).1
  refine wmain_domAt_mono hN (fun _ => ?_) hε hD (h Ω W hW hP z hz v hv)
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have := wmain_mW_im_nonneg hN (specOf A) hzim
  have := (wmain_psi_pos hN (specOf A) hzim).le
  positivity

/-- Monotonicity of the anisotropic law in `D`. -/
private lemma wmain_aniso_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ} {ε D D' : ℝ}
    (hD : D' ≤ D) (h : AnisotropicLawWAt N ε D A W S) : AnisotropicLawWAt N ε D' A W S := by
  intro z hz v w
  have h1 := h z hz v w
  unfold DomAt at h1 ⊢
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

private lemma wmain_eig_decompH {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      M = U * diagonal hM.eigenvalues * Uᵀ := by
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

private lemma wmain_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hMU : M = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ :=
  Matrix.inv_eq_right_inv (wmain_right_inv hUU hUU' hMU hne)

private lemma wmain_ent_sandwich_sq {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
    (v : Fin N → ℝ) :
    ent (cplx U * diagonal d * (cplx U)ᵀ) v v = ∑ k, d k * ((((Uᵀ *ᵥ v) k) ^ 2 : ℝ) : ℂ) := by
  rw [wmain_ent_sandwich]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  ring

/-- `Im Π_{vv} ≤ τ⁻² (1 + κ⁻¹) Im m` for `|v| = 1`, `κ = (3τ⁻¹ + 1)⁻²`, under the standing bound,
on `𝐃^W(τ, N)`. -/
private lemma wmain_im_piW_le {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ)
    {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hnA : ‖A‖ ≤ τ⁻¹) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hz : z ∈ S) (hzD : z ∈ domW τ N) {v : Fin N → ℝ} (hv : testNorm v = 1) :
    (ent (piW A z) v v).im ≤ τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) * (mW (specOf A) z).im := by
  obtain ⟨hzim, hzE, -, hzη⟩ := hzD
  set m := mW (specOf A) z with hm
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i => (abs_specOf_le_norm hA i).trans hnA
  have hmge : ((3 * τ⁻¹ + 1) ^ 2)⁻¹ * z.im ≤ m.im := im_mW_ge hN hτ ha hzim hzE hzη
  have hm0 : 0 < m.im := (mW_spec hN (specOf A) hzim).1
  obtain ⟨U, hUU, hUU', hAU⟩ := wmain_eig_decompH hA
  have hd : ∀ k, τ ≤ ‖(hA.eigenvalues k : ℂ) - (m + z)‖ := by
    intro k
    have h := hS z hz k
    rw [specOf_eq hA] at h
    have e : -(mW hA.eigenvalues z) + (hA.eigenvalues k : ℂ) - z
        = (hA.eigenvalues k : ℂ) - (mW hA.eigenvalues z + z) := by ring
    rw [e] at h
    rwa [hm, specOf_eq hA]
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - (m + z) ≠ 0 := fun k h0 => by
    have := hd k
    rw [h0, norm_zero] at this
    linarith
  have hpi : piW A z = (cplx U) * diagonal
      (fun k => ((hA.eigenvalues k : ℂ) - (m + z))⁻¹) * (cplx U)ᵀ :=
    wmain_resolvent_eq hUU hUU' hAU hne
  rw [hpi, wmain_ent_sandwich_sq, Complex.im_sum]
  have hsq : ∑ k, ((Uᵀ *ᵥ v) k) ^ 2 = 1 := by
    have h := wmain_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v
    rw [hv] at h
    unfold testNorm at h
    have := Real.sqrt_eq_one.1 h
    simpa using this
  have hw : (m + z).im = m.im + z.im := by simp
  have hterm : ∀ k, (((hA.eigenvalues k : ℂ) - (m + z))⁻¹ *
      ((((Uᵀ *ᵥ v) k) ^ 2 : ℝ) : ℂ)).im ≤ ((Uᵀ *ᵥ v) k) ^ 2 * ((m.im + z.im) / τ ^ 2) := by
    intro k
    rw [Complex.im_mul_ofReal]
    have h1 : (((hA.eigenvalues k : ℂ) - (m + z))⁻¹).im =
        (m + z).im / Complex.normSq ((hA.eigenvalues k : ℂ) - (m + z)) := by
      rw [Complex.inv_im]
      simp
    have hns : τ ^ 2 ≤ Complex.normSq ((hA.eigenvalues k : ℂ) - (m + z)) := by
      rw [← Complex.sq_norm]
      exact pow_le_pow_left₀ hτ.le (hd k) 2
    rw [h1, hw, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) hns
  calc ∑ k, (((hA.eigenvalues k : ℂ) - (m + z))⁻¹ * ((((Uᵀ *ᵥ v) k) ^ 2 : ℝ) : ℂ)).im
      ≤ ∑ k, ((Uᵀ *ᵥ v) k) ^ 2 * ((m.im + z.im) / τ ^ 2) := Finset.sum_le_sum fun k _ => hterm k
    _ = (m.im + z.im) / τ ^ 2 := by rw [← Finset.sum_mul, hsq, one_mul]
    _ ≤ τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) * m.im := by
        have hκ : z.im ≤ (3 * τ⁻¹ + 1) ^ 2 * m.im := by
          have hK : 0 < (3 * τ⁻¹ + 1) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hmge hK.le
          rwa [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at this
        rw [div_eq_mul_inv, ← inv_pow]
        have h := mul_le_mul_of_nonneg_left hκ (sq_nonneg τ⁻¹)
        have e : (m.im + z.im) * τ⁻¹ ^ 2 = τ⁻¹ ^ 2 * m.im + τ⁻¹ ^ 2 * z.im := by ring
        have e2 : τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) * m.im =
            τ⁻¹ ^ 2 * m.im + τ⁻¹ ^ 2 * ((3 * τ⁻¹ + 1) ^ 2 * m.im) := by ring
        rw [e, e2]
        linarith [h]

/-- (C_m) implies (A_m), via `Im Π_{vv} ≤ τ⁻²(1 + κ⁻¹) Im m`. -/
private lemma wmain_propA_of_propC {N : ℕ} {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    {P : ModelClassW N} {C : ℕ → ℝ} {C₀ δ ε D : ℝ} {m : ℕ} (hset : WigSetting τ N A S)
    (hN : 1 ≤ N) (hε : τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) ≤ (N : ℝ) ^ ε)
    (h : PropCW N C P A S C₀ δ m ε D) : PropAW N C P A S C₀ δ m ε D := by
  intro Ω _ _ W hW hP z hz v hv
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have hzim : 0 < z.im := hzD.1
  have hm : 0 < (mW (specOf A) z).im := (mW_spec hN (specOf A) hzim).1
  have hPi := wmain_im_piW_le hN hset.pos hset.symmA hset.normA hset.standing hzS hzD hv
  have hK : τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) * (mW (specOf A) z).im ≤
      (N : ℝ) ^ ε * (mW (specOf A) z).im := mul_le_mul_of_nonneg_right hε hm.le
  have hC := h Ω W hW hP z hz v hv
  unfold ODomAt DomAt at hC
  unfold DomAt
  refine le_trans (measure_mono fun ω hω => ?_) hC
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hG : (ent (GW A (W ω) z) v v).im ≤ (ent (piW A z) v v).im +
      ‖ent (GW A (W ω) z - piW A z) v v‖ := by
    rw [wmain_ent_sub]
    have := Complex.im_le_norm (ent (GW A (W ω) z) v v - ent (piW A z) v v)
    simp only [Complex.sub_im] at this
    linarith
  rw [mul_add] at hω
  linarith

private lemma wmain_testBilin_smul_left {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) : testBilin (a • v) B w = a * testBilin v B w := by
  have e : (fun s => (((a • v) s : ℝ) : ℂ)) = (a : ℂ) • fun s => (v s : ℂ) := by
    funext s
    simp
  unfold testBilin
  rw [e, smul_dotProduct, smul_eq_mul]

private lemma wmain_testBilin_smul_right {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) : testBilin v B (a • w) = a * testBilin v B w := by
  have e : (fun s => (((a • w) s : ℝ) : ℂ)) = (a : ℂ) • fun s => (w s : ℂ) := by
    funext s
    simp
  unfold testBilin
  rw [e, mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma wmain_testNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    testNorm v ^ 2 = ∑ s, v s ^ 2 := by
  unfold testNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma wmain_testNorm_smul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    testNorm (a • v) = |a| * testNorm v := by
  unfold testNorm
  have e : ∑ s, (a • v) s ^ 2 = a ^ 2 * ∑ s, v s ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

private lemma wmain_eq_zero_of_testNorm {ι : Type*} [Fintype ι] {v : ι → ℝ}
    (h : testNorm v = 0) : v = 0 := by
  have h2 : ∑ s, v s ^ 2 = 0 := by
    rw [← wmain_testNorm_sq, h]
    ring
  funext s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (v t)).1 h2 s
    (Finset.mem_univ s)
  simpa using this

/-- From the diagonal bound for unit vectors, `|⟨a, B a⟩| ≤ |a|² N^ε Y` off an event of
probability at most `N^{−(D+1)}`, for every `a`. -/
private lemma wmain_diag_event {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ι : Type*} [Fintype ι]
    {B : Ω → Matrix ι ι ℂ} {ε D Y : ℝ}
    (h : ∀ u : ι → ℝ, testNorm u = 1 →
      DomAt N ε (D + 1) (fun ω => ‖testBilin u (B ω) u‖) (fun _ => Y)) (a : ι → ℝ) :
    ∃ E : Set Ω, ℙ E ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) ∧
      ∀ ω ∉ E, ‖testBilin a (B ω) a‖ ≤ testNorm a ^ 2 * ((N : ℝ) ^ ε * Y) := by
  by_cases ha : testNorm a = 0
  · refine ⟨∅, by simp, fun ω _ => ?_⟩
    have h0 := wmain_eq_zero_of_testNorm ha
    subst h0
    rw [ha]
    simp [testBilin]
  · set u : ι → ℝ := (testNorm a)⁻¹ • a with hu
    have hpos : 0 < testNorm a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
    have hu1 : testNorm u = 1 := by
      rw [hu, wmain_testNorm_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ ha]
    have hau : a = testNorm a • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ ha, one_smul]
    refine ⟨{ω | (N : ℝ) ^ ε * Y < ‖testBilin u (B ω) u‖}, h u hu1, fun ω hω => ?_⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hω
    have e : testBilin a (B ω) a = ((testNorm a ^ 2 : ℝ) : ℂ) * testBilin u (B ω) u := by
      conv_lhs => rw [hau]
      rw [wmain_testBilin_smul_left, wmain_testBilin_smul_right]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hω (sq_nonneg _)

/-- Polarization: the diagonal bounds `|⟨u, B u⟩| ≺ Y` on the unit sphere, for a symmetric `B`,
give `|⟨v, B w⟩| ≺ Y |v| |w|` for all `v, w`, at the cost `D + 1 ↦ D`. -/
private lemma wmain_bilin_of_diag {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ι : Type*} [Fintype ι]
    {B : Ω → Matrix ι ι ℂ} (hB : ∀ ω, (B ω)ᵀ = B ω) {ε D Y : ℝ} (hN : 2 ≤ N)
    (h : ∀ u : ι → ℝ, testNorm u = 1 →
      DomAt N ε (D + 1) (fun ω => ‖testBilin u (B ω) u‖) (fun _ => Y)) (v w : ι → ℝ) :
    DomAt N ε D (fun ω => ‖testBilin v (B ω) w‖) (fun _ => Y * testNorm v * testNorm w) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold DomAt
  by_cases hv0 : testNorm v = 0
  · have h0 := wmain_eq_zero_of_testNorm hv0
    subst h0
    have he : {ω | (N : ℝ) ^ ε * (Y * testNorm (0 : ι → ℝ) * testNorm w) <
        ‖testBilin 0 (B ω) w‖} = ∅ := by
      ext ω
      simp [testBilin, hv0]
    rw [he, measure_empty]
    simp
  by_cases hw0 : testNorm w = 0
  · have h0 := wmain_eq_zero_of_testNorm hw0
    subst h0
    have he : {ω | (N : ℝ) ^ ε * (Y * testNorm v * testNorm (0 : ι → ℝ)) <
        ‖testBilin v (B ω) 0‖} = ∅ := by
      ext ω
      simp [testBilin, hw0, show (fun _ : ι => (0 : ℂ)) = 0 from rfl]
    rw [he, measure_empty]
    simp
  have hvp : 0 < testNorm v := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv0)
  have hwp : 0 < testNorm w := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hw0)
  set v' : ι → ℝ := (testNorm v)⁻¹ • v with hv'
  set w' : ι → ℝ := (testNorm w)⁻¹ • w with hw'
  have hv1 : testNorm v' = 1 := by
    rw [hv', wmain_testNorm_smul, abs_inv, abs_of_pos hvp, inv_mul_cancel₀ hv0]
  have hw1 : testNorm w' = 1 := by
    rw [hw', wmain_testNorm_smul, abs_inv, abs_of_pos hwp, inv_mul_cancel₀ hw0]
  have hvv : v = testNorm v • v' := by rw [hv', smul_smul, mul_inv_cancel₀ hv0, one_smul]
  have hww : w = testNorm w • w' := by rw [hw', smul_smul, mul_inv_cancel₀ hw0, one_smul]
  have hsum : testNorm (v' + w') ^ 2 + testNorm (v' - w') ^ 2 = 4 := by
    have h1 := wmain_testNorm_sq v'
    have h2 := wmain_testNorm_sq w'
    rw [hv1] at h1
    rw [hw1] at h2
    rw [wmain_testNorm_sq, wmain_testNorm_sq, ← Finset.sum_add_distrib]
    have e : ∀ s, (v' + w') s ^ 2 + (v' - w') s ^ 2 = 2 * v' s ^ 2 + 2 * w' s ^ 2 := fun s => by
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← h1, ← h2]
    norm_num
  obtain ⟨Ea, hEa, ha⟩ := wmain_diag_event (B := B) h (v' + w')
  obtain ⟨Eb, hEb, hb⟩ := wmain_diag_event (B := B) h (v' - w')
  have hsub : {ω | (N : ℝ) ^ ε * (Y * testNorm v * testNorm w) <
      ‖testBilin v (B ω) w‖} ⊆ Ea ∪ Eb := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    have hA := ha ω hnot.1
    have hB' := hb ω hnot.2
    have hpol := testBilin_polar (B ω) (hB ω) v' w'
    have e : testBilin v (B ω) w =
        ((testNorm v * testNorm w : ℝ) : ℂ) * testBilin v' (B ω) w' := by
      conv_lhs => rw [hvv, hww]
      rw [wmain_testBilin_smul_left, wmain_testBilin_smul_right]
      push_cast
      ring
    have hnorm : ‖testBilin v' (B ω) w'‖ ≤ (N : ℝ) ^ ε * Y := by
      rw [hpol, norm_div]
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [h4, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      calc ‖testBilin (v' + w') (B ω) (v' + w') - testBilin (v' - w') (B ω) (v' - w')‖
          ≤ ‖testBilin (v' + w') (B ω) (v' + w')‖ + ‖testBilin (v' - w') (B ω) (v' - w')‖ :=
            norm_sub_le _ _
        _ ≤ testNorm (v' + w') ^ 2 * ((N : ℝ) ^ ε * Y) +
            testNorm (v' - w') ^ 2 * ((N : ℝ) ^ ε * Y) := add_le_add hA hB'
        _ = (N : ℝ) ^ ε * Y * 4 := by
          rw [← add_mul, hsum]
          ring
    have hfin : ‖testBilin v (B ω) w‖ ≤ (N : ℝ) ^ ε * (Y * testNorm v * testNorm w) := by
      rw [e, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg hvp.le hwp.le)]
      have hvw : 0 ≤ testNorm v * testNorm w := mul_nonneg hvp.le hwp.le
      calc testNorm v * testNorm w * ‖testBilin v' (B ω) w'‖
          ≤ testNorm v * testNorm w * ((N : ℝ) ^ ε * Y) := mul_le_mul_of_nonneg_left hnorm hvw
        _ = _ := by ring
    exact absurd hω (not_lt.2 hfin)
  have hNe : 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
    have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * N := by
      rw [← Real.rpow_add_one hNpos.ne']
      ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left hNr (Real.rpow_nonneg hNpos.le _) |>.trans_eq' (by ring)
  calc ℙ {ω | (N : ℝ) ^ ε * (Y * testNorm v * testNorm w) < ‖testBilin v (B ω) w‖}
      ≤ ℙ (Ea ∪ Eb) := measure_mono hsub
    _ ≤ ℙ Ea + ℙ Eb := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hEa hEb
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)]
        ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hNe

/-- `G^W − Π^W` is symmetric for real symmetric `W`, `A`. -/
private lemma wmain_GW_sub_piW_symm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) (z : ℂ) : (GW A Wm z - piW A z)ᵀ = GW A Wm z - piW A z := by
  have hA' : Aᵀ = A := by
    have := hA.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have h1 : (GW A Wm z)ᵀ = GW A Wm z := by
    unfold GW
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    congr 1
    rw [← Matrix.transpose_map, Matrix.transpose_add, hW, hA']
  have h2 : (piW A z)ᵀ = piW A z := by
    unfold piW
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    congr 1
    rw [← Matrix.transpose_map, hA']
  rw [Matrix.transpose_sub, h1, h2]

private lemma wmain_le_rpow' {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) {N : ℕ}
    (h : ⌈Q ^ a⁻¹⌉₊ ≤ N) : Q ≤ (N : ℝ) ^ a := by
  have h1 : Q ^ a⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  calc Q = (Q ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hQ ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hQ _) h1 ha.le

/-- Enlarging the moment function keeps a matrix in the class. -/
private lemma wmain_class_mono {Ω : Type*} [MeasureSpace Ω] {C C' : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (h : WigClassEntries C N W) (hC : ∀ p, C p ≤ C' p) :
    WigClassEntries C' N W :=
  { h with moment := fun p i j => (h.moment p i j).trans (hC p) }

/-! ## The comparison induction -/

/-- Relaxing a domination: if `N^{ε'} ζ ≤ N^{ε} ζ'` pointwise and `D ≤ D'`, then `ξ ≺ ζ` at
`(ε', D')` gives `ξ ≺ ζ'` at `(ε, D)`. -/
private lemma wmain_dom_relax {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {ε ε' D D' : ℝ} {ξ ζ ζ' : Ω → ℝ} (hζ : ∀ ω, (N : ℝ) ^ ε' * ζ ω ≤ (N : ℝ) ^ ε * ζ' ω)
    (hD : D ≤ D') (h : DomAt N ε' D' ξ ζ) : DomAt N ε D ξ ζ' := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold DomAt at h ⊢
  refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (hζ ω) hω

/-- On the top level `m* = max(1, ⌈(1 − τ)/δ⌉)`, the level set is all of `S ⊆ 𝐃^W(τ, N)`. -/
private lemma wmain_levelSet_top {N : ℕ} (hN : 1 ≤ N) {τ δ : ℝ} (hδ : 0 < δ) {S : Set ℂ}
    (hS : S ⊆ domW τ N) : levelSet N δ S (topLevel τ δ) = S := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  ext z
  refine ⟨fun hz => hz.1, fun hz => ⟨hz, ?_⟩⟩
  obtain ⟨-, -, hηl, -⟩ := hS hz
  refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1r ?_) hηl
  have h1 : (1 - τ) / δ ≤ (topLevel τ δ : ℝ) := by
    unfold topLevel
    push_cast
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have h3 : 1 - τ ≤ δ * (topLevel τ δ : ℝ) := by
    have := (div_le_iff₀ hδ).1 h1
    linarith
  linarith

/-- For `τ > 1` the domain `𝐃^W(τ, N)` is empty (`N ≥ 1`), hence so is every `S ⊆ 𝐃^W(τ, N)`. -/
private lemma wmain_eq_empty {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 1 < τ) {S : Set ℂ}
    (hS : S ⊆ domW τ N) : S = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨-, -, hηl, hηu⟩ := hS hz
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) := Real.one_le_rpow hN1r (by linarith)
  have h2 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hτ
  linarith

/-- (A_l) for the whole class at every level `l ≤ L`, from (A_0) and the induction step; the
class is `P` with vanishing third moments or any class under `Ψ^W ≤ N^{−1/4−c₀}`. -/
private lemma wmain_levels (τ c₀ : ℝ) (C : ℕ → ℝ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4)
    (hδc : 2 * (C₀ + 5) * δ ≤ c₀) (L : ℕ) :
    ∀ D : ℝ, ∃ DG : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (P : ModelClassW N), WigSetting τ N A S → (P = zeroThirdW ∨ PsiSmallW c₀ (specOf A) S) →
      AnisotropicLawWAt N δ DG A (goeW N) S →
      ∀ l ≤ L, PropAW N (momMaxW C) P A S C₀ δ l (δ / 8) D := by
  induction L with
  | zero =>
    intro D
    obtain ⟨N₀, h₀⟩ := wig_propA_zero τ (momMaxW C) (δ / 8) D hτ hτ1 (by positivity)
    refine ⟨0, N₀, fun N hN A S P hset _ _ l hl => ?_⟩
    obtain rfl : l = 0 := by omega
    exact h₀ N hN A S P C₀ δ hset (by linarith) hδ.le
  | succ L ih =>
    intro D
    obtain ⟨DG, DA, Nc, hc⟩ := wig_propC_of_propA τ c₀ C C₀ δ (max D 0) hτ hτ1 hc₀ hδ hC₀ hC₀δ
      hδc (le_max_right _ _)
    obtain ⟨DG', N', h'⟩ := ih (max D DA)
    set Kτ : ℝ := τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) with hKτ
    have hKτ0 : 0 ≤ Kτ := by positivity
    refine ⟨max DG DG', max (max N' Nc) (max 1 ⌈Kτ ^ (δ / 8)⁻¹⌉₊), ?_⟩
    intro N hN A S P hset hP hG l hl
    have hN' : N' ≤ N := by omega
    have hNc : Nc ≤ N := by omega
    have hN1 : 1 ≤ N := by omega
    have hNK : ⌈Kτ ^ (δ / 8)⁻¹⌉₊ ≤ N := by omega
    have hGc := wmain_aniso_mono hN1 (le_max_left _ _) hG
    have hG' := wmain_aniso_mono hN1 (le_max_right _ _) hG
    have hall := h' N hN' A S P hset hP hG'
    rcases Nat.lt_or_ge l (L + 1) with hlt | hge
    · exact wmain_propA_mono hset hN1 le_rfl (le_max_left _ _) (hall l (by omega))
    · obtain rfl : l = L + 1 := by omega
      have hA : PropAW N (momMaxW C) P A S C₀ δ (L + 1 - 1) (δ / 4) DA := by
        rw [show L + 1 - 1 = L by omega]
        exact wmain_propA_mono hset hN1 (by linarith) (le_max_right _ _) (hall L le_rfl)
      have hC := hc N hNc A S (L + 1) P hset (by omega) hP hGc hA
      exact wmain_propA_mono hset hN1 le_rfl (le_max_left _ _)
        (wmain_propA_of_propC hset hN1 (wmain_le_rpow' hKτ0 (by positivity) hNK) hC)

/-- Propositions 7.1/8.1 analogue: the anisotropic law for `(W^Gauss, A, S)` at `(ε₁, D₁)` gives
the anisotropic law for every `W` of the class, under (a) or (b). -/
theorem wig_comparison (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ → WigClassEntries C N W → SpectralDomainW τ N S →
      StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      AnisotropicLawWAt N ε₁ D₁ A (goeW N) S →
      AnisotropicLawWAt N ε D A W S := by
  by_cases hτ1 : τ ≤ 1
  swap
  · push Not at hτ1
    refine ⟨1, 0, one_pos, 1, ?_⟩
    intro N hN Ω _ _ A W S _ _ _ hS _ _ _
    have hN1 : 1 ≤ N := hN
    rw [wmain_eq_empty hN1 hτ1 hS.1]
    intro z hz
    exact absurd hz (Set.notMem_empty z)
  set δ : ℝ := min (min ε τ) c₀ / 200 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos (lt_min (lt_min hε hτ) hc₀) (by norm_num)
  have hδε : δ ≤ ε / 200 := by
    rw [hδdef]
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  have hδτ : δ ≤ τ / 200 := by
    rw [hδdef]
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  have hδc : δ ≤ c₀ / 200 := by
    rw [hδdef]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hC₀δ : (30 : ℝ) * δ ≤ τ / 4 := by linarith
  have hδc' : 2 * ((30 : ℝ) + 5) * δ ≤ c₀ := by linarith
  obtain ⟨DG0, DA, Nc, hc⟩ := wig_propC_of_propA τ c₀ C 30 δ (max D 0 + 1) hτ hτ1 hc₀ hδ
    (le_refl _) hC₀δ hδc' (by positivity)
  obtain ⟨DG1, N1, h1⟩ := wmain_levels τ c₀ C 30 δ hτ hτ1 hc₀ hδ (le_refl _) hC₀δ hδc'
    (topLevel τ δ - 1) DA
  refine ⟨δ, max DG0 DG1, hδ, max (max Nc N1) 2, ?_⟩
  intro N hN Ω _ _ A W S hA hnA hW hS hb hP hG
  have hNc : Nc ≤ N := by omega
  have hN1' : N1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hset : WigSetting τ N A S := ⟨hτ, hτ1, hA, hnA, hS, hb⟩
  have hcl : WigClassEntries (momMaxW C) N W :=
    wmain_class_mono hW fun p => le_max_left _ _
  have hGc := wmain_aniso_mono hN1 (le_max_left _ _) hG
  have hG1 := wmain_aniso_mono hN1 (le_max_right _ _) hG
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have key : ∀ P : ModelClassW N, (P = zeroThirdW ∨ PsiSmallW c₀ (specOf A) S) → P Ω W →
      AnisotropicLawWAt N ε D A W S := by
    intro P hPP hPW
    have hlev := h1 N hN1' A S P hset hPP hG1
    have hA' : PropAW N (momMaxW C) P A S 30 δ (topLevel τ δ - 1) (δ / 4) DA :=
      wmain_propA_mono hset hN1 (by linarith) le_rfl (hlev _ le_rfl)
    have hCm := hc N hNc A S (topLevel τ δ) P hset (le_max_left _ _) hPP hGc hA'
    intro z hz v w
    have hzl : z ∈ levelSet N δ S (topLevel τ δ) := by
      rw [wmain_levelSet_top hN1 hδ hS.1]
      exact hz
    have hdiag : ∀ u : Fin N → ℝ, testNorm u = 1 →
        DomAt N (δ / 8) (max D 0 + 1) (fun ω => ‖testBilin u (GW A (W ω) z - piW A z) u‖)
          (fun _ => (N : ℝ) ^ ((30 : ℝ) * δ) * PsiW (specOf A) z) :=
      fun u hu => hCm Ω W hcl hPW z hzl u hu
    have hpol := wmain_bilin_of_diag (B := fun ω => GW A (W ω) z - piW A z)
      (fun ω => wmain_GW_sub_piW_symm hA (hW.symm ω) z) (D := max D 0) hN2 hdiag v w
    refine wmain_dom_relax hN1 (ε' := δ / 8) (D' := max D 0) (fun ω => ?_) (le_max_left _ _) hpol
    have hΨ := (wmain_psi_pos hN1 (specOf A) (hset.domain.1 hz).1).le
    have hvw : 0 ≤ testNorm v * testNorm w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hexp : (N : ℝ) ^ (δ / 8) * (N : ℝ) ^ ((30 : ℝ) * δ) ≤ (N : ℝ) ^ ε := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    have hX : 0 ≤ PsiW (specOf A) z * (testNorm v * testNorm w) := mul_nonneg hΨ hvw
    calc (N : ℝ) ^ (δ / 8) * ((N : ℝ) ^ ((30 : ℝ) * δ) * PsiW (specOf A) z * testNorm v *
          testNorm w)
        = ((N : ℝ) ^ (δ / 8) * (N : ℝ) ^ ((30 : ℝ) * δ)) *
          (PsiW (specOf A) z * (testNorm v * testNorm w)) := by ring
      _ ≤ (N : ℝ) ^ ε * (PsiW (specOf A) z * (testNorm v * testNorm w)) :=
          mul_le_mul_of_nonneg_right hexp hX
      _ = (N : ℝ) ^ ε * (PsiW (specOf A) z * testNorm v * testNorm w) := by ring
  rcases hP with h3 | hPs
  · exact key zeroThirdW (Or.inl rfl) h3
  · exact key allModelsW (Or.inr hPs) trivial

/-- Theorem 12.2 (i) for the class: the entrywise law for `(W^Gauss, D, S)` at `(ε₁, D₁)` gives
the anisotropic law for `(W, A, S)` at `(ε, D)`, for every `W` of the class, under (a) or (b). -/
theorem general_wig_aniso_class (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ → WigClassEntries C N W → SpectralDomainW τ N S →
      StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AnisotropicLawWAt N ε D A W S := by
  obtain ⟨ε₁', D₁', hε₁', N₁, h1⟩ := wig_comparison τ c₀ C ε D hτ hc₀ hε
  obtain ⟨N₂, h2⟩ := goe_aniso_diag τ ε₁' D₁' hτ hε₁'
  refine ⟨ε₁' / 4, lawD1 ε₁' D₁', by positivity, max N₁ N₂, ?_⟩
  intro N hN Ω _ _ A W S hA hnA hW hS hb hP hg
  have hgd : AnisotropicLawWAt N ε₁' D₁' (diagonal (specOf A)) (goeW N) S :=
    h2 N (by omega) (specOf A) (goeW N) S (isGOE_goeW N) hS.1 hg
  exact h1 N (by omega) A W S hA hnA hW hS hb hP (goe_aniso_rotate hA (isGOE_goeW N) hgd)

/-- Theorem 12.2 (i) (`lem:general Wig`) at fixed `N`. -/
theorem general_wig_aniso (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WignerModel τ C N A W → SpectralDomainW τ N S → StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AnisotropicLawWAt N ε D A W S := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := general_wig_aniso_class τ c₀ C ε D hτ hc₀ hε
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN Ω _ _ A W S hm hS hb hab hg =>
    h N hN A W S hm.symmA hm.normA hm.entries.toClass hS hb hab hg⟩

/-- Theorem 12.2 (i) with the interval-support condition of §12.1 (the literal form). -/
theorem general_wig_aniso_lit (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (Lm Lp : ℝ),
      WignerModel τ C N A W → IntervalSupportW (specOf A) Lm Lp → SpectralDomainW τ N S →
      StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AnisotropicLawWAt N ε D A W S := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := general_wig_aniso τ c₀ C ε D hτ hc₀ hε
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN Ω _ _ A W S _ _ hm _ hS hb hab hg =>
    h N hN A W S hm hS hb hab hg⟩

/-- Theorem 12.2 (i) instantiated along `N ≥ N₀` at `(wigRad N, aEx N)`, `τ = 1/2`, `S = 𝐃^W`,
case (a); conditional on the entrywise law for the GOE. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N) →
    AnisotropicLawWAt N 1 1 (aEx N) (wigRad N) (domW (1 / 2) N) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    general_wig_aniso (1 / 2) (1 / 12) (fun _ => 1) 1 1 (by norm_num) (by norm_num) one_pos
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 hg =>
    h N hN (aEx N) (wigRad N) (domW (1 / 2) N) (wignerModel_rad hN1)
      (spectralDomainW_domW _ _) (standingBoundW_aEx hN1) (Or.inl (wigRad_third N)) hg⟩

/-! ## Instances (conditional on the laws for the Gaussian matrix)

The hypotheses on the model are discharged at `(wigRad N, aEx N, 𝐃^W(1/2, N))` for every `N ≥ 1`:
`aEx N` is symmetric, not diagonal and of norm at most `1/4 ≤ τ⁻¹`, the Rademacher entries
satisfy (a), and the standing bound holds. The laws for the Gaussian matrix are deformed local
laws that cannot be discharged at a fixed `N`; they stay as binders. -/

/-- Theorem 12.2 (i) for the class at `(wigRad N, aEx N)`, `τ = 1/2`, `S = 𝐃^W`, case (a);
conditional on the entrywise law for the GOE. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N) →
    AnisotropicLawWAt N 1 1 (aEx N) (wigRad N) (domW (1 / 2) N) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    general_wig_aniso_class (1 / 2) (1 / 12) (fun _ => 1) 1 1 (by norm_num) (by norm_num) one_pos
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 hg =>
    h N hN (aEx N) (wigRad N) (domW (1 / 2) N) (aEx_isHermitian N)
      ((norm_aEx_le hN1).trans (by norm_num)) (wignerEntries_wigRad hN1).toClass
      (spectralDomainW_domW _ _) (standingBoundW_aEx hN1) (Or.inl (wigRad_third N)) hg⟩

/-- The comparison at `(wigRad N, aEx N)`, `τ = 1/2`, `S = 𝐃^W`, case (a); conditional on the
anisotropic law for the GOE with the same `A`. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    AnisotropicLawWAt N ε₁ D₁ (aEx N) (goeW N) (domW (1 / 2) N) →
    AnisotropicLawWAt N 1 1 (aEx N) (wigRad N) (domW (1 / 2) N) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    wig_comparison (1 / 2) (1 / 12) (fun _ => 1) 1 1 (by norm_num) (by norm_num) one_pos
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 hg =>
    h N hN (aEx N) (wigRad N) (domW (1 / 2) N) (aEx_isHermitian N)
      ((norm_aEx_le hN1).trans (by norm_num)) (wignerEntries_wigRad hN1).toClass
      (spectralDomainW_domW _ _) (standingBoundW_aEx hN1) (Or.inl (wigRad_third N)) hg⟩

/-- The literal form at `(wigRad N, aEx N)`, `τ = 1/2`, `S = 𝐃^W`, case (a); conditional on the
entrywise law for the GOE and on the interval-support condition, which stays a binder. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Lm Lp : ℝ,
    IntervalSupportW (specOf (aEx N)) Lm Lp →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N) →
    AnisotropicLawWAt N 1 1 (aEx N) (wigRad N) (domW (1 / 2) N) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    general_wig_aniso_lit (1 / 2) (1 / 12) (fun _ => 1) 1 1 (by norm_num) (by norm_num) one_pos
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 Lm Lp hI hg =>
    h N hN (aEx N) (wigRad N) (domW (1 / 2) N) Lm Lp (wignerModel_rad hN1) hI
      (spectralDomainW_domW _ _) (standingBoundW_aEx hN1) (Or.inl (wigRad_third N)) hg⟩

#print axioms general_wig_aniso_class
#print axioms general_wig_aniso
#print axioms general_wig_aniso_lit
#print axioms wig_comparison

end Anisotropic
