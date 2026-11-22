module

public import Anisotropic.Comparison.Props
public import Anisotropic.Comparison.Words
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.Props
public import Anisotropic.Wigner.RoughBound
public import Anisotropic.Wigner.SelfConsistent
public import Anisotropic.Wigner.SelfConsistentII
public import Anisotropic.Wigner.Words

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Lemma 12.8: the averaged coefficients for every order (including `n = 3`) -/

/-- `F̃(W) = |N⁻¹ tr G − m|`. -/
def FtW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ‖mNW A Wm z - mW (specOf A) z‖

/-- The coefficient of `t^k` in `N⁻¹ tr G − m` along the entry `(i, j)`. -/
def avgCoeffW {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N) (k : ℕ) : ℂ :=
  (-1) ^ k * (N : ℂ)⁻¹ * trace (GW A Wm z * (deltaW i j * GW A Wm z) ^ k)
    - if k = 0 then mW (specOf A) z else 0

/-! ## Resolvents of real symmetric matrices -/

section Resolvent

variable {N : ℕ}

/-- `∑_c |y_c|²` for a complex vector `y`. -/
private def awNsq (y : Fin N → ℂ) : ℝ := ∑ c, ‖y c‖ ^ 2

private lemma awNsq_nonneg (y : Fin N → ℂ) : 0 ≤ awNsq y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For a real symmetric `H`, `∑_a conj((H y)_a) y_a` is real. -/
private lemma aw_im_quad {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) (y : Fin N → ℂ) :
    (∑ a, starRingEnd ℂ ((cplx H *ᵥ y) a) * y a).im = 0 := by
  set q := ∑ a, starRingEnd ℂ ((cplx H *ᵥ y) a) * y a with hq
  have hsym : ∀ a b, H b a = H a b := fun a b => by
    have := congrFun (congrFun hH a) b
    rw [Matrix.transpose_apply] at this
    exact this
  have e1 : q = ∑ a, ∑ b, (H a b : ℂ) * (starRingEnd ℂ (y b) * y a) := by
    rw [hq]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.mulVec, dotProduct, cplx, Matrix.map_apply, map_sum, map_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Complex.conj_ofReal]
    ring
  have e2 : starRingEnd ℂ q = q := by
    rw [e1, map_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj, hsym a b]
    ring
  exact Complex.conj_eq_iff_im.1 e2

/-- If `(H − w) y = v` with `H` real symmetric, then `Im ∑_a conj(v_a) y_a = Im w ∑ |y_a|²`. -/
private lemma aw_ward_of_eq {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ}
    {y v : Fin N → ℂ} (hv : (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ y = v) :
    (∑ a, starRingEnd ℂ (v a) * y a).im = w.im * awNsq y := by
  have hva : ∀ a, v a = (cplx H *ᵥ y) a - w * y a := fun a => by
    rw [← hv, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have e : ∑ a, starRingEnd ℂ (v a) * y a =
      ∑ a, starRingEnd ℂ ((cplx H *ᵥ y) a) * y a -
        starRingEnd ℂ w * ∑ a, ((‖y a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hva a, map_sub, map_mul, sub_mul]
    congr 1
    rw [mul_assoc]
    congr 1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, Complex.sub_im, aw_im_quad hH y, ← Complex.ofReal_sum]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_add, awNsq]
  ring

/-- `H − w` is invertible for `H` real symmetric and `Im w > 0`. -/
private lemma aw_isUnit_det {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ}
    (hw : 0 < w.im) : IsUnit (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h := aw_ward_of_eq hH hMy
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, Complex.zero_im] at h
  have hn : awNsq y = 0 := by
    have := mul_eq_zero.1 h.symm
    rcases this with h1 | h1
    · linarith
    · exact h1
  apply hy
  funext c
  have hc : ‖y c‖ ^ 2 = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖y a‖)).1 hn c
      (Finset.mem_univ c)
    exact this
  simpa using hc

/-- `(H − w) (H − w)⁻¹ = 1`. -/
private lemma aw_mul_inv {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ}
    (hw : 0 < w.im) :
    (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (aw_isUnit_det hH hw)

/-- `(H − w)⁻¹` is symmetric for `H` real symmetric. -/
private lemma aw_inv_transpose {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) (w : ℂ) :
    ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᵀ =
      (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  congr 1
  rw [cplx, ← Matrix.transpose_map, hH]

/-- Ward identity: `Im ⟨v, (H − w)⁻¹ v⟩ = Im w · |(H − w)⁻¹ v|²`. -/
private lemma aw_ward {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ} (hw : 0 < w.im)
    (v : Fin N → ℂ) :
    (∑ a, starRingEnd ℂ (v a) *
        ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v) a).im =
      w.im * awNsq ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v) := by
  refine aw_ward_of_eq hH ?_
  rw [Matrix.mulVec_mulVec, aw_mul_inv hH hw, Matrix.one_mulVec]

/-- `|(H − w)⁻¹ v|² ≤ (Im w)⁻² |v|²`. -/
private lemma aw_opNorm {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ} (hw : 0 < w.im)
    (v : Fin N → ℂ) :
    w.im ^ 2 * awNsq ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v) ≤ awNsq v := by
  set y := (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v with hy
  have hW := aw_ward hH hw v
  rw [← hy] at hW
  have h1 : w.im * awNsq y ≤ ∑ a, ‖v a‖ * ‖y a‖ := by
    rw [← hW]
    refine (Complex.im_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : (∑ a, ‖v a‖ * ‖y a‖) ^ 2 ≤ awNsq v * awNsq y :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h0 : 0 ≤ w.im * awNsq y := mul_nonneg hw.le (awNsq_nonneg y)
  have h3 : (w.im * awNsq y) ^ 2 ≤ awNsq v * awNsq y :=
    (pow_le_pow_left₀ h0 h1 2).trans h2
  have hy0 := awNsq_nonneg y
  rcases hy0.lt_or_eq with hpos | hzero
  · have : w.im ^ 2 * awNsq y * awNsq y ≤ awNsq v * awNsq y := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero, mul_zero]
    exact awNsq_nonneg v

end Resolvent

/-! ## `G^W` and `Π^W` -/

section GPi

variable {N : ℕ}

private lemma aw_symm_of_herm {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  have h := hA.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at h

private lemma aw_symm_add {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) : (Wm + A)ᵀ = Wm + A := by
  rw [Matrix.transpose_add, hW, aw_symm_of_herm hA]

private lemma aw_GW_eq (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    GW A Wm z = (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl

private lemma aw_piW_eq (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    piW A z = (cplx A - (mW (specOf A) z + z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl

/-- `G` is symmetric. -/
private lemma aw_GW_symm {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    (z : ℂ) (a b : Fin N) : GW A Wm z b a = GW A Wm z a b := by
  have h := aw_inv_transpose (aw_symm_add hA hW) z
  rw [← aw_GW_eq] at h
  have := congrFun (congrFun h a) b
  rwa [Matrix.transpose_apply] at this

/-- `testBilin x M x` as a sesquilinear sum. -/
private lemma aw_testBilin_eq (x : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    testBilin x M x = ∑ a, starRingEnd ℂ (cvec x a) * (M *ᵥ cvec x) a := by
  simp [testBilin, dotProduct, cvec, Complex.conj_ofReal]

/-- Ward identity for `G`: `Im ⟨x, G x⟩ = η |G x|²`. -/
private lemma aw_GW_ward {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    {z : ℂ} (hz : 0 < z.im) (x : Fin N → ℝ) :
    (testBilin x (GW A Wm z) x).im = z.im * awNsq (GW A Wm z *ᵥ cvec x) := by
  rw [aw_testBilin_eq, aw_GW_eq]
  exact aw_ward (aw_symm_add hA hW) hz _

/-- `|G v|² ≤ η⁻² |v|²`. -/
private lemma aw_GW_op {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℂ) :
    z.im ^ 2 * awNsq (GW A Wm z *ᵥ v) ≤ awNsq v := by
  rw [aw_GW_eq]
  exact aw_opNorm (aw_symm_add hA hW) hz v

private lemma aw_im_w_pos {A : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) {z : ℂ} (hz : 0 < z.im) :
    0 < (mW (specOf A) z + z).im := by
  have := (mW_spec hN (specOf A) hz).1
  simp only [Complex.add_im]
  linarith

/-- Ward identity for `Π`: `Im ⟨x, Π x⟩ = (Im m + η) |Π x|²`. -/
private lemma aw_piW_ward {A : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (x : Fin N → ℝ) :
    (testBilin x (piW A z) x).im =
      (mW (specOf A) z + z).im * awNsq (piW A z *ᵥ cvec x) := by
  rw [aw_testBilin_eq, aw_piW_eq]
  exact aw_ward (aw_symm_of_herm hA) (aw_im_w_pos hN hz) _

private lemma aw_testNorm_sq (x : Fin N → ℝ) : testNorm x ^ 2 = ∑ c, x c ^ 2 := by
  rw [testNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- From a bilinear bound `|⟨v, M x⟩| ≤ T |v| |x|` on real vectors: `|M x|² ≤ 2 T² |x|²`. -/
private lemma aw_nsq_le_of_bilin {M : Matrix (Fin N) (Fin N) ℂ} {T : ℝ} (x : Fin N → ℝ)
    (hM : ∀ v : Fin N → ℝ, ‖testBilin v M x‖ ≤ T * testNorm v * testNorm x) :
    awNsq (M *ᵥ cvec x) ≤ 2 * T ^ 2 * testNorm x ^ 2 := by
  set y := M *ᵥ cvec x with hy
  set yR : Fin N → ℝ := fun c => (y c).re
  set yI : Fin N → ℝ := fun c => (y c).im
  have hR : testBilin yR M x = ∑ c, ((y c).re : ℂ) * y c := by
    simp [testBilin, dotProduct, yR, hy]
  have hI : testBilin yI M x = ∑ c, ((y c).im : ℂ) * y c := by
    simp [testBilin, dotProduct, yI, hy]
  have hsum : awNsq y = (testBilin yR M x).re + (testBilin yI M x).im := by
    rw [hR, hI, Complex.re_sum, Complex.im_sum, awNsq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnR : testNorm yR ^ 2 + testNorm yI ^ 2 = awNsq y := by
    rw [aw_testNorm_sq, aw_testNorm_sq, awNsq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : awNsq y ≤ T * testNorm x * (testNorm yR + testNorm yI) := by
    rw [hsum]
    have a1 := (Complex.re_le_norm (testBilin yR M x)).trans (hM yR)
    have a2 := (Complex.im_le_norm (testBilin yI M x)).trans (hM yI)
    nlinarith
  have hx0 : 0 ≤ testNorm x := Real.sqrt_nonneg _
  have hR0 : 0 ≤ testNorm yR := Real.sqrt_nonneg _
  have hI0 : 0 ≤ testNorm yI := Real.sqrt_nonneg _
  have hy0 : 0 ≤ awNsq y := awNsq_nonneg y
  have h2 : awNsq y ^ 2 ≤ (T * testNorm x) ^ 2 * (2 * awNsq y) := by
    have e := pow_le_pow_left₀ hy0 h1 2
    have : (testNorm yR + testNorm yI) ^ 2 ≤ 2 * awNsq y := by
      rw [← hnR]; nlinarith [sq_nonneg (testNorm yR - testNorm yI)]
    calc awNsq y ^ 2 ≤ (T * testNorm x * (testNorm yR + testNorm yI)) ^ 2 := e
      _ = (T * testNorm x) ^ 2 * (testNorm yR + testNorm yI) ^ 2 := by ring
      _ ≤ (T * testNorm x) ^ 2 * (2 * awNsq y) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
  rcases hy0.lt_or_eq with hpos | hzero
  · have : awNsq y * awNsq y ≤ (2 * T ^ 2 * testNorm x ^ 2) * awNsq y := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

/-- The real orthogonal matrix of eigenvectors of a symmetric `A`. -/
private lemma aw_eig_decomp {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- `(A − w)⁻¹ = U diag((λₖ − w)⁻¹) Uᵀ` for `A = U diag(λ) Uᵀ`. -/
private lemma aw_resolvent_eq {A U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx A - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ := by
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx A - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - w) * (cplx U)ᵀ := by
    have h1 : cplx A = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hAU]
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

/-- `N⁻¹ tr Π = m` (the equation of `m^W`). -/
private lemma aw_trace_piW {A : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : (N : ℂ)⁻¹ * trace (piW A z) = mW (specOf A) z := by
  obtain ⟨U, hUU, hUU', hAU⟩ := aw_eig_decomp hA
  have hw := aw_im_w_pos (A := A) hN hz
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - (mW (specOf A) z + z) ≠ 0 := fun k h0 => by
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
    linarith
  have hpi : piW A z = (cplx U) * diagonal
      (fun k => ((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹) * (cplx U)ᵀ :=
    aw_resolvent_eq hUU hUU' hAU hne
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have htr : trace (piW A z) =
      ∑ k, ((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹ := by
    rw [hpi, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP', Matrix.one_mul,
      Matrix.trace_diagonal]
  have hspec := (mW_spec hN (specOf A) hz).2
  rw [htr]
  conv_rhs => rw [hspec]
  rw [stieltjesA, specOf_eq hA, add_comm z]

end GPi

/-! ## The coefficients `a_k` along an entry -/

section Coeff

variable {N : ℕ}

private lemma aw_delta_eq {i j : Fin N} (hij : i ≠ j) :
    deltaW i j = single i j (1 : ℂ) + single j i 1 := by
  ext a b
  simp only [deltaW, Matrix.add_apply, Matrix.single_apply]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : a = j <;> by_cases h4 : b = i <;>
    subst_vars <;> simp_all [eq_comm]

/-- `tr(G (Δ G)^{k+1}) = tr((Δ G)^k Δ G²)`. -/
private lemma aw_trace_eq (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (k : ℕ) :
    trace (G * (deltaW i j * G) ^ (k + 1)) =
      trace ((deltaW i j * G) ^ k * deltaW i j * (G * G)) := by
  rw [pow_succ, show G * ((deltaW i j * G) ^ k * (deltaW i j * G)) =
    (G * ((deltaW i j * G) ^ k * deltaW i j)) * G by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]

private lemma aw_trace_mul (K H : Matrix (Fin N) (Fin N) ℂ) :
    trace (K * H) = ∑ b, ∑ c, K b c * H c b := by
  simp [Matrix.trace, Matrix.mul_apply]

/-- `G²` is symmetric when `G` is. -/
private lemma aw_sq_symm {G : Matrix (Fin N) (Fin N) ℂ} (hG : ∀ a b, G b a = G a b) (a b : Fin N) :
    (G * G) b a = (G * G) a b := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hG c a, hG b c, mul_comm]

private lemma aw_tr1 {i j : Fin N} (hij : i ≠ j) {G : Matrix (Fin N) (Fin N) ℂ}
    (hG : ∀ a b, G b a = G a b) :
    trace (G * (deltaW i j * G) ^ 1) = 2 * (G * G) i j := by
  rw [aw_trace_eq G i j 0, pow_zero, Matrix.one_mul, aw_delta_eq hij]
  simp only [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, smul_eq_mul, one_mul]
  rw [aw_sq_symm hG i j]
  ring

private lemma aw_tr2 {i j : Fin N} (hij : i ≠ j) {G : Matrix (Fin N) (Fin N) ℂ}
    (hG : ∀ a b, G b a = G a b) :
    trace (G * (deltaW i j * G) ^ 2) =
      2 * G i j * (G * G) i j + G i i * (G * G) j j + G j j * (G * G) i i := by
  rw [aw_trace_eq G i j 1, pow_one, aw_delta_eq hij]
  have hHs := aw_sq_symm hG
  generalize G * G = H at hHs ⊢
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_mul_single, Matrix.trace_add,
    Matrix.trace_single_mul, smul_eq_mul, one_mul, mul_one]
  rw [hHs i j, hG i j]
  ring

private lemma aw_tr3 {i j : Fin N} (hij : i ≠ j) {G : Matrix (Fin N) (Fin N) ℂ}
    (hG : ∀ a b, G b a = G a b) :
    trace (G * (deltaW i j * G) ^ 3) =
      2 * (G i j ^ 2 * (G * G) i j + G i i * G j j * (G * G) i j +
        G i j * G j j * (G * G) i i + G i j * G i i * (G * G) j j) := by
  rw [aw_trace_eq G i j 2, pow_two, aw_delta_eq hij]
  have hHs := aw_sq_symm hG
  generalize G * G = H at hHs ⊢
  simp only [← Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_mul_single, Matrix.trace_add,
    Matrix.trace_single_mul, smul_eq_mul, one_mul, mul_one]
  rw [hHs i j, hG i j]
  ring

/-- A nonnegative function supported on `{i, j}` sums to at most `f i + f j`. -/
private lemma aw_sum_two (f : Fin N → ℝ) (i j : Fin N) (h0 : ∀ d, 0 ≤ f d)
    (hs : ∀ d, d ≠ i → d ≠ j → f d = 0) : ∑ d, f d ≤ f i + f j := by
  have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub fun d _ hd => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    exact hs d hd.1 hd.2]
  by_cases hij : i = j
  · subst hij
    simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton]
    linarith [h0 i]
  · rw [Finset.sum_pair hij]

private lemma aw_delta_ne {i j a b : Fin N} (h : deltaW i j a b ≠ 0) :
    (a = i ∨ a = j) ∧ (b = i ∨ b = j) := by
  simp only [deltaW] at h
  split_ifs at h with h1
  · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h1, Or.inl h2⟩
  · exact absurd rfl h

private lemma aw_norm_delta_le (i j a b : Fin N) : ‖deltaW i j a b‖ ≤ 1 := by
  simp only [deltaW]
  split_ifs <;> simp

/-- `K_l = (Δ G)^l Δ` is supported on `{i, j}²`, with entries at most `(4B)^l`. -/
private lemma aw_K_bound {G : Matrix (Fin N) (Fin N) ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a b, ‖G a b‖ ≤ B) (i j : Fin N) (l : ℕ) :
    ∀ a b, (((deltaW i j * G) ^ l * deltaW i j) a b ≠ 0 → (a = i ∨ a = j) ∧ (b = i ∨ b = j)) ∧
      ‖((deltaW i j * G) ^ l * deltaW i j) a b‖ ≤ (4 * B) ^ l := by
  induction l with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_mul]
    exact ⟨aw_delta_ne, by simpa using aw_norm_delta_le i j a b⟩
  | succ l ih =>
    set K := (deltaW i j * G) ^ l * deltaW i j with hK
    have hK' : (deltaW i j * G) ^ (l + 1) * deltaW i j = deltaW i j * (G * K) := by
      rw [pow_succ', hK]; simp only [Matrix.mul_assoc]
    intro a b
    rw [hK']
    have hentry : (deltaW i j * (G * K)) a b = ∑ c, deltaW i j a c * ∑ d, G c d * K d b := by
      simp [Matrix.mul_apply]
    rw [hentry]
    constructor
    · intro hne
      constructor
      · by_contra hc
        apply hne
        refine Finset.sum_eq_zero fun c _ => ?_
        have : deltaW i j a c = 0 := by
          by_contra h'
          exact hc (aw_delta_ne h').1
        rw [this, zero_mul]
      · by_contra hc
        apply hne
        refine Finset.sum_eq_zero fun c _ => ?_
        have : ∑ d, G c d * K d b = 0 := Finset.sum_eq_zero fun d _ => by
          have : K d b = 0 := by
            by_contra h'
            exact hc ((ih d b).1 h').2
          rw [this, mul_zero]
        rw [this, mul_zero]
    · have hin : ∀ c, ‖∑ d, G c d * K d b‖ ≤ 2 * (B * (4 * B) ^ l) := by
        intro c
        refine (norm_sum_le _ _).trans ?_
        have := aw_sum_two (fun d => ‖G c d * K d b‖) i j (fun d => norm_nonneg _)
          (fun d h1 h2 => by
          have : K d b = 0 := by
            by_contra h'
            rcases ((ih d b).1 h').1 with h | h
            · exact h1 h
            · exact h2 h
          simp [this])
        refine this.trans ?_
        have e1 : ∀ d, ‖G c d * K d b‖ ≤ B * (4 * B) ^ l := fun d => by
          rw [norm_mul]
          exact mul_le_mul (hB c d) (ih d b).2 (norm_nonneg _) hB0
        linarith [e1 i, e1 j]
      refine (norm_sum_le _ _).trans ?_
      have := aw_sum_two (fun c => ‖deltaW i j a c * ∑ d, G c d * K d b‖) i j
        (fun c => norm_nonneg _) (fun c h1 h2 => by
          have : deltaW i j a c = 0 := by
            by_contra h'
            rcases (aw_delta_ne h').2 with h | h
            · exact h1 h
            · exact h2 h
          simp [this])
      refine this.trans ?_
      have e1 : ∀ c, ‖deltaW i j a c * ∑ d, G c d * K d b‖ ≤ 2 * (B * (4 * B) ^ l) := fun c => by
        rw [norm_mul]
        calc ‖deltaW i j a c‖ * ‖∑ d, G c d * K d b‖ ≤ 1 * (2 * (B * (4 * B) ^ l)) :=
              mul_le_mul (aw_norm_delta_le i j a c) (hin c) (norm_nonneg _) zero_le_one
          _ = 2 * (B * (4 * B) ^ l) := one_mul _
      calc _ ≤ 2 * (B * (4 * B) ^ l) + 2 * (B * (4 * B) ^ l) := add_le_add (e1 i) (e1 j)
        _ = (4 * B) ^ (l + 1) := by ring

/-- `|tr(G (ΔG)^{k+1})| ≤ 4 (4B)^k h` when `|G_{ab}| ≤ B` and `|(G²)_{ab}| ≤ h`. -/
private lemma aw_trace_le {G : Matrix (Fin N) (Fin N) ℂ} {B h : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a b, ‖G a b‖ ≤ B) (hh : ∀ a b, ‖(G * G) a b‖ ≤ h) (i j : Fin N) (k : ℕ) :
    ‖trace (G * (deltaW i j * G) ^ (k + 1))‖ ≤ 4 * (4 * B) ^ k * h := by
  rw [aw_trace_eq, aw_trace_mul]
  set K := (deltaW i j * G) ^ k * deltaW i j with hK
  have hKb := aw_K_bound hB0 hB i j k
  have hh0 : 0 ≤ h := (norm_nonneg _).trans (hh i i)
  have hrow : ∀ b, ‖∑ c, K b c * (G * G) c b‖ ≤ 2 * ((4 * B) ^ k * h) := by
    intro b
    refine (norm_sum_le _ _).trans ?_
    have := aw_sum_two (fun c => ‖K b c * (G * G) c b‖) i j (fun c => norm_nonneg _)
      (fun c h1 h2 => by
        have : K b c = 0 := by
          by_contra h'
          rcases ((hKb b c).1 h').2 with h | h
          · exact h1 h
          · exact h2 h
        simp [this])
    refine this.trans ?_
    have e1 : ∀ c, ‖K b c * (G * G) c b‖ ≤ (4 * B) ^ k * h := fun c => by
      rw [norm_mul]
      exact mul_le_mul (hKb b c).2 (hh c b) (norm_nonneg _) (by positivity)
    linarith [e1 i, e1 j]
  refine (norm_sum_le _ _).trans ?_
  have := aw_sum_two (fun b => ‖∑ c, K b c * (G * G) c b‖) i j (fun b => norm_nonneg _)
    (fun b h1 h2 => by
      have : ∀ c, K b c = 0 := fun c => by
        by_contra h'
        rcases ((hKb b c).1 h').1 with h | h
        · exact h1 h
        · exact h2 h
      simp [this])
  refine this.trans ?_
  linarith [hrow i, hrow j]

/-- `|a_{k+1}| ≤ 4 (4B)^k h / N`. -/
private lemma aw_avgCoeff_le {A Wm : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {B h : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hh : ∀ a b, ‖(GW A Wm z * GW A Wm z) a b‖ ≤ h)
    (i j : Fin N) (k : ℕ) :
    ‖avgCoeffW A Wm z i j (k + 1)‖ ≤ 4 * (4 * B) ^ k * h / N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold avgCoeffW
  simp only [Nat.add_one_ne_zero, ite_false, sub_zero, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_inv, Complex.norm_natCast]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (aw_trace_le hB0 hB hh i j k) (inv_nonneg.2 hN)

private lemma aw_avgCoeff_zero (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N) :
    avgCoeffW A Wm z i j 0 = mNW A Wm z - mW (specOf A) z := by
  simp [avgCoeffW, mNW]

end Coeff

/-! ## Deterministic sums of resolvent entries -/

section Sums

variable {N : ℕ}

private lemma aw_le_of_sq {S M : ℝ} (hM : 0 ≤ M) (h : S ^ 2 ≤ M ^ 2) : S ≤ M :=
  (abs_le_of_sq_le_sq' h hM).2

/-- Cauchy–Schwarz for a sum of products of norms, bounded through the two squared sums. -/
private lemma aw_cs {ι : Type*} [Fintype ι] (f g : ι → ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hf : ∑ i, f i ^ 2 ≤ X ^ 2) (hg : ∑ i, g i ^ 2 ≤ Y ^ 2) : ∑ i, f i * g i ≤ X * Y := by
  refine aw_le_of_sq (mul_nonneg hX hY) ?_
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ f g).trans ?_
  rw [mul_pow]
  exact mul_le_mul hf hg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

/-- `∑_i |x_i| ≤ √N (∑ |x_i|²)^{1/2}`. -/
private lemma aw_sum_le_sqrt (x : Fin N → ℝ) {X : ℝ} (hX : 0 ≤ X) (h : ∑ i, x i ^ 2 ≤ X ^ 2) :
    ∑ i, x i ≤ Real.sqrt N * X := by
  have := aw_cs (fun _ => (1 : ℝ)) x (Real.sqrt_nonneg N) hX (by
    simp [Real.sq_sqrt (Nat.cast_nonneg N)]) h
  simpa using this

/-- The hypotheses on a fixed matrix used for the order-three sums: `G` symmetric with
`‖G‖ ≤ η⁻¹`, columns of `G` bounded by `ℓ`, `|G − P| ≤ u`, `|G| ≤ B`, `|P| ≤ T`, columns of `P`
bounded by `√2 T`, weights `|σ| ≤ 1`, and the bounds `μ`, `Γ` on `G t` for the vectors
`t = (σ_{ij} P_{ii})_i` and `t = (σ_{ij} P_{jj})_j`. -/
private structure AwEv (N : ℕ) (G P : Matrix (Fin N) (Fin N) ℂ) (σ : Fin N → Fin N → ℂ)
    (η ℓ μ Γ u B T : ℝ) : Prop where
  eta : 0 < η
  ell : 0 ≤ ℓ
  mu : 0 ≤ μ
  gam : 0 ≤ Γ
  u0 : 0 ≤ u
  B0 : 0 ≤ B
  T0 : 0 ≤ T
  symm : ∀ a b, G b a = G a b
  op : ∀ v : Fin N → ℂ, η ^ 2 * awNsq (G *ᵥ v) ≤ awNsq v
  col : ∀ a, awNsq (fun c => G c a) ≤ ℓ ^ 2
  tilde : ∀ a b, ‖G a b - P a b‖ ≤ u
  bdd : ∀ a b, ‖G a b‖ ≤ B
  piB : ∀ a b, ‖P a b‖ ≤ T
  piCol : ∀ a, awNsq (fun c => P c a) ≤ 2 * T ^ 2
  sig : ∀ i j, ‖σ i j‖ ≤ 1
  f1 : ∀ j, awNsq (G *ᵥ fun i => σ i j * P i i) ≤ μ ^ 2
  f1s : ∀ j, awNsq (G *ᵥ star fun i => σ i j * P i i) ≤ μ ^ 2
  f2 : ∀ i, awNsq (G *ᵥ fun j => σ i j * P j j) ≤ μ ^ 2
  f2s : ∀ i, awNsq (G *ᵥ star fun j => σ i j * P j j) ≤ μ ^ 2
  e1 : ∀ j, ‖(G *ᵥ fun i => σ i j * P i i) j‖ ≤ Γ
  e2 : ∀ i, ‖(G *ᵥ fun j => σ i j * P j j) i‖ ≤ Γ

section Ev

variable {G P : Matrix (Fin N) (Fin N) ℂ} {σ : Fin N → Fin N → ℂ} {η ℓ μ Γ u B T : ℝ}

private lemma AwEv.H_le (h : AwEv N G P σ η ℓ μ Γ u B T) (a b : Fin N) :
    ‖(G * G) a b‖ ≤ ℓ ^ 2 := by
  have e : (G * G) a b = ∑ c, G c a * G c b := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [h.symm c a]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  have := aw_cs (fun c => ‖G c a‖) (fun c => ‖G c b‖) h.ell h.ell (h.col a) (h.col b)
  simpa [sq] using this

/-- `η² ∑_i |(G²)_{ij}|² ≤ ℓ²`. -/
private lemma AwEv.Hcol (h : AwEv N G P σ η ℓ μ Γ u B T) (j : Fin N) :
    η ^ 2 * ∑ i, ‖(G * G) i j‖ ^ 2 ≤ ℓ ^ 2 := by
  have e : (G *ᵥ fun c => G c j) = fun i => (G * G) i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have := h.op (fun c => G c j)
  rw [e] at this
  exact this.trans (h.col j)

private lemma AwEv.sumG (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ∑ i, ∑ j, ‖G i j‖ ≤ N * (Real.sqrt N * ℓ) := by
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, ‖G i j‖ ≤ Real.sqrt N * ℓ := fun j =>
    aw_sum_le_sqrt (fun i => ‖G i j‖) h.ell (h.col j)
  calc _ ≤ ∑ _j : Fin N, Real.sqrt N * ℓ := Finset.sum_le_sum fun j _ => this j
    _ = _ := by simp

private lemma AwEv.sumH2 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    η ^ 2 * ∑ i, ∑ j, ‖(G * G) i j‖ ^ 2 ≤ N * ℓ ^ 2 := by
  rw [Finset.sum_comm, Finset.mul_sum]
  calc _ ≤ ∑ _j : Fin N, ℓ ^ 2 := Finset.sum_le_sum fun j _ => h.Hcol j
    _ = _ := by simp

private lemma AwEv.sumH (h : AwEv N G P σ η ℓ μ Γ u B T) :
    η * ∑ i, ∑ j, ‖(G * G) i j‖ ≤ N * (Real.sqrt N * ℓ) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  have : ∀ j, η * ∑ i, ‖(G * G) i j‖ ≤ Real.sqrt N * ℓ := fun j => by
    rw [Finset.mul_sum]
    refine aw_sum_le_sqrt (fun i => η * ‖(G * G) i j‖) h.ell ?_
    have := h.Hcol j
    simp_rw [mul_pow, ← Finset.mul_sum]
    exact this
  calc _ ≤ ∑ _j : Fin N, Real.sqrt N * ℓ := Finset.sum_le_sum fun j _ => this j
    _ = _ := by simp

private lemma AwEv.sumHP (h : AwEv N G P σ η ℓ μ Γ u B T) :
    η * ∑ i, ∑ j, ‖(G * G) i j‖ * ‖P i j‖ ≤ 2 * N * ℓ * T := by
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type' (fun i j => η * (‖(G * G) i j‖ * ‖P i j‖))]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : ∑ x : Fin N × Fin N, (η * ‖(G * G) x.1 x.2‖) ^ 2 ≤ (Real.sqrt N * ℓ) ^ 2 := by
    rw [Fintype.sum_prod_type' (fun i j => (η * ‖(G * G) i j‖) ^ 2)]
    simp_rw [mul_pow, ← Finset.mul_sum]
    rw [Real.sq_sqrt hN0]
    exact h.sumH2
  have h2 : ∑ x : Fin N × Fin N, ‖P x.1 x.2‖ ^ 2 ≤ (Real.sqrt N * (2 * T)) ^ 2 := by
    rw [Fintype.sum_prod_type' (fun i j => ‖P i j‖ ^ 2), Finset.sum_comm, mul_pow,
      Real.sq_sqrt hN0]
    calc _ ≤ ∑ _j : Fin N, 2 * T ^ 2 := Finset.sum_le_sum fun j _ => h.piCol j
      _ ≤ ∑ _j : Fin N, (2 * T) ^ 2 := Finset.sum_le_sum fun j _ => by nlinarith [h.T0]
      _ = _ := by simp
  have := aw_cs (fun x : Fin N × Fin N => η * ‖(G * G) x.1 x.2‖) (fun x => ‖P x.1 x.2‖)
    (mul_nonneg (Real.sqrt_nonneg _) h.ell) (mul_nonneg (Real.sqrt_nonneg _) (by linarith [h.T0]))
    h1 h2
  calc _ = ∑ x : Fin N × Fin N, (η * ‖(G * G) x.1 x.2‖) * ‖P x.1 x.2‖ :=
        Finset.sum_congr rfl fun x _ => by ring
    _ ≤ _ := this
    _ = Real.sqrt N * Real.sqrt N * 2 * ℓ * T := by ring
    _ = 2 * N * ℓ * T := by rw [Real.mul_self_sqrt hN0]; ring

/-- `|∑_i t_i (G²)_{ij}| ≤ μ ℓ` when `|G t| ≤ μ`. -/
private lemma AwEv.fam (h : AwEv N G P σ η ℓ μ Γ u B T) (t : Fin N → ℂ)
    (ht : awNsq (G *ᵥ t) ≤ μ ^ 2) (j : Fin N) :
    ‖∑ i, t i * (G * G) i j‖ ≤ μ * ℓ := by
  have e : ∑ i, t i * (G * G) i j = ∑ c, (G *ᵥ t) c * G c j := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
    rw [h.symm c i]
    ring
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact aw_cs _ _ h.mu h.ell ht (h.col j)

/-- `|∑_i t_i conj((G²)_{ij})| ≤ μ ℓ` when `|G t̄| ≤ μ`. -/
private lemma AwEv.famc (h : AwEv N G P σ η ℓ μ Γ u B T) (t : Fin N → ℂ)
    (ht : awNsq (G *ᵥ star t) ≤ μ ^ 2) (j : Fin N) :
    ‖∑ i, t i * starRingEnd ℂ ((G * G) i j)‖ ≤ μ * ℓ := by
  have e : ∑ i, t i * starRingEnd ℂ ((G * G) i j) =
      starRingEnd ℂ (∑ i, (star t) i * (G * G) i j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Pi.star_apply]
  rw [e, Complex.norm_conj]
  exact h.fam (star t) ht j

private lemma aw_norm_sum2 (f : Fin N → Fin N → ℂ) :
    ‖∑ i, ∑ j, f i j‖ ≤ ∑ i, ∑ j, ‖f i j‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)

private lemma AwEv.sumG2 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ∑ i, ∑ j, ‖G i j‖ ^ 2 ≤ N * ℓ ^ 2 := by
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _j : Fin N, ℓ ^ 2 := Finset.sum_le_sum fun j _ => h.col j
    _ = _ := by simp

private lemma AwEv.sumH' (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ∑ i, ∑ j, ‖(G * G) i j‖ ≤ N * (Real.sqrt N * ℓ) / η := by
  rw [le_div_iff₀ h.eta, mul_comm]
  exact h.sumH

/-- The order-three sum `∑ σ_{ij} G_{ij}² (G²)_{ij}`. -/
private lemma AwEv.S1 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ‖∑ i, ∑ j, σ i j * (G i j ^ 2 * (G * G) i j)‖ ≤ N * ℓ ^ 4 := by
  refine (aw_norm_sum2 _).trans ?_
  have : ∀ i j, ‖σ i j * (G i j ^ 2 * (G * G) i j)‖ ≤ ℓ ^ 2 * ‖G i j‖ ^ 2 := fun i j => by
    rw [norm_mul, norm_mul, norm_pow]
    have := h.sig i j
    have := h.H_le i j
    have h0 : 0 ≤ ‖G i j‖ ^ 2 := sq_nonneg _
    calc ‖σ i j‖ * (‖G i j‖ ^ 2 * ‖(G * G) i j‖) ≤ 1 * (‖G i j‖ ^ 2 * ℓ ^ 2) := by gcongr
      _ = ℓ ^ 2 * ‖G i j‖ ^ 2 := by ring
  calc _ ≤ ∑ i, ∑ j, ℓ ^ 2 * ‖G i j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => this i j
    _ = ℓ ^ 2 * ∑ i, ∑ j, ‖G i j‖ ^ 2 := by simp_rw [Finset.mul_sum]
    _ ≤ ℓ ^ 2 * (N * ℓ ^ 2) := mul_le_mul_of_nonneg_left h.sumG2 (sq_nonneg _)
    _ = N * ℓ ^ 4 := by ring

/-- The order-three sum `∑ σ_{ij} G_{ii} G_{jj} (G²)_{ij}`. -/
private lemma AwEv.S2 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ‖∑ i, ∑ j, σ i j * (G i i * G j j * (G * G) i j)‖ ≤
      N * B * (μ * ℓ) + N * u * (μ * ℓ) + u ^ 2 * (N * (Real.sqrt N * ℓ) / η) := by
  set D := G - P with hD
  have hsplit : ∀ i j, σ i j * (G i i * G j j * (G * G) i j) =
      G j j * ((σ i j * P i i) * (G * G) i j) + D i i * ((σ i j * P j j) * (G * G) j i) +
        σ i j * (D i i * D j j * (G * G) i j) := fun i j => by
    rw [aw_sq_symm h.symm j i]
    simp only [hD, Matrix.sub_apply]
    ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin N, B * (μ * ℓ) := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (h.bdd j j) (h.fam _ (h.f1 j) j) (norm_nonneg _) h.B0
      _ = _ := by simp; ring
  · simp_rw [← Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : Fin N, u * (μ * ℓ) := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          refine mul_le_mul ?_ (h.fam _ (h.f2 i) i) (norm_nonneg _) h.u0
          simpa [hD] using h.tilde i i
      _ = _ := by simp; ring
  · refine (aw_norm_sum2 _).trans ?_
    have : ∀ i j, ‖σ i j * (D i i * D j j * (G * G) i j)‖ ≤ u ^ 2 * ‖(G * G) i j‖ := fun i j => by
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖D i i‖ ≤ u := by simpa [hD] using h.tilde i i
      have h2 : ‖D j j‖ ≤ u := by simpa [hD] using h.tilde j j
      have := h.sig i j
      have := h.u0
      calc ‖σ i j‖ * (‖D i i‖ * ‖D j j‖ * ‖(G * G) i j‖) ≤ 1 * (u * u * ‖(G * G) i j‖) := by
            gcongr
        _ = u ^ 2 * ‖(G * G) i j‖ := by ring
    calc _ ≤ ∑ i, ∑ j, u ^ 2 * ‖(G * G) i j‖ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => this i j
      _ = u ^ 2 * ∑ i, ∑ j, ‖(G * G) i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h.sumH' (sq_nonneg _)

/-- The order-three sum `∑ σ_{ij} G_{ij} G_{jj} (G²)_{ii}`. -/
private lemma AwEv.S3 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ‖∑ i, ∑ j, σ i j * (G i j * G j j * (G * G) i i)‖ ≤
      N * (ℓ ^ 2 * Γ) + u * ℓ ^ 2 * (N * (Real.sqrt N * ℓ)) := by
  set D := G - P with hD
  have hsplit : ∀ i j, σ i j * (G i j * G j j * (G * G) i i) =
      (G * G) i i * (G i j * (σ i j * P j j)) + σ i j * (G i j * D j j * (G * G) i i) :=
    fun i j => by simp only [hD, Matrix.sub_apply]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simp_rw [← Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : Fin N, ℓ ^ 2 * Γ := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          refine mul_le_mul (h.H_le i i) ?_ (norm_nonneg _) (sq_nonneg _)
          have := h.e2 i
          simpa [Matrix.mulVec, dotProduct] using this
      _ = _ := by simp
  · refine (aw_norm_sum2 _).trans ?_
    have : ∀ i j, ‖σ i j * (G i j * D j j * (G * G) i i)‖ ≤ u * ℓ ^ 2 * ‖G i j‖ := fun i j => by
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖D j j‖ ≤ u := by simpa [hD] using h.tilde j j
      have := h.sig i j
      have := h.H_le i i
      have := h.u0
      calc ‖σ i j‖ * (‖G i j‖ * ‖D j j‖ * ‖(G * G) i i‖) ≤ 1 * (‖G i j‖ * u * ℓ ^ 2) := by
            gcongr
        _ = u * ℓ ^ 2 * ‖G i j‖ := by ring
    calc _ ≤ ∑ i, ∑ j, u * ℓ ^ 2 * ‖G i j‖ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => this i j
      _ = u * ℓ ^ 2 * ∑ i, ∑ j, ‖G i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h.sumG (mul_nonneg h.u0 (sq_nonneg _))

/-- The order-three sum `∑ σ_{ij} G_{ij} G_{ii} (G²)_{jj}`. -/
private lemma AwEv.S4 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ‖∑ i, ∑ j, σ i j * (G i j * G i i * (G * G) j j)‖ ≤
      N * (ℓ ^ 2 * Γ) + u * ℓ ^ 2 * (N * (Real.sqrt N * ℓ)) := by
  set D := G - P with hD
  have hsplit : ∀ i j, σ i j * (G i j * G i i * (G * G) j j) =
      (G * G) j j * (G j i * (σ i j * P i i)) + σ i j * (G i j * D i i * (G * G) j j) :=
    fun i j => by rw [h.symm i j]; simp only [hD, Matrix.sub_apply]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin N, ℓ ^ 2 * Γ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          refine mul_le_mul (h.H_le j j) ?_ (norm_nonneg _) (sq_nonneg _)
          have := h.e1 j
          simpa [Matrix.mulVec, dotProduct] using this
      _ = _ := by simp
  · refine (aw_norm_sum2 _).trans ?_
    have : ∀ i j, ‖σ i j * (G i j * D i i * (G * G) j j)‖ ≤ u * ℓ ^ 2 * ‖G i j‖ := fun i j => by
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖D i i‖ ≤ u := by simpa [hD] using h.tilde i i
      have := h.sig i j
      have := h.H_le j j
      have := h.u0
      calc ‖σ i j‖ * (‖G i j‖ * ‖D i i‖ * ‖(G * G) j j‖) ≤ 1 * (‖G i j‖ * u * ℓ ^ 2) := by
            gcongr
        _ = u * ℓ ^ 2 * ‖G i j‖ := by ring
    calc _ ≤ ∑ i, ∑ j, u * ℓ ^ 2 * ‖G i j‖ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => this i j
      _ = u * ℓ ^ 2 * ∑ i, ∑ j, ‖G i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h.sumG (mul_nonneg h.u0 (sq_nonneg _))

/-- `x` or `conj x`. -/
private def awCj (b : Bool) (x : ℂ) : ℂ := if b then starRingEnd ℂ x else x

private lemma awCj_norm (b : Bool) (x : ℂ) : ‖awCj b x‖ = ‖x‖ := by
  cases b <;> simp [awCj]

/-- The sum of the four order-three words: `tr(G (ΔG)³) = 2 awTr3`. -/
private def awTr3 (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ℂ :=
  G i j ^ 2 * (G * G) i j + G i i * G j j * (G * G) i j +
    G i j * G j j * (G * G) i i + G i j * G i i * (G * G) j j

/-- The order-two words: `tr(G (ΔG)²) = awTr2`. -/
private def awTr2 (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ℂ :=
  2 * G i j * (G * G) i j + G i i * (G * G) j j + G j j * (G * G) i i

private lemma AwEv.Q1 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ‖∑ i, ∑ j, σ i j * awTr3 G i j‖ ≤
      N * ℓ ^ 4 + (N * B * (μ * ℓ) + N * u * (μ * ℓ) + u ^ 2 * (N * (Real.sqrt N * ℓ) / η)) +
        2 * (N * (ℓ ^ 2 * Γ) + u * ℓ ^ 2 * (N * (Real.sqrt N * ℓ))) := by
  have e : ∑ i, ∑ j, σ i j * awTr3 G i j =
      ∑ i, ∑ j, σ i j * (G i j ^ 2 * (G * G) i j) +
        ∑ i, ∑ j, σ i j * (G i i * G j j * (G * G) i j) +
        ∑ i, ∑ j, σ i j * (G i j * G j j * (G * G) i i) +
        ∑ i, ∑ j, σ i j * (G i j * G i i * (G * G) j j) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [awTr3]
    ring
  rw [e]
  set X1 := ∑ i, ∑ j, σ i j * (G i j ^ 2 * (G * G) i j)
  set X2 := ∑ i, ∑ j, σ i j * (G i i * G j j * (G * G) i j)
  set X3 := ∑ i, ∑ j, σ i j * (G i j * G j j * (G * G) i i)
  set X4 := ∑ i, ∑ j, σ i j * (G i j * G i i * (G * G) j j)
  have t1 := norm_add_le (X1 + X2 + X3) X4
  have t2 := norm_add_le (X1 + X2) X3
  have t3 := norm_add_le X1 X2
  have h1 := h.S1
  have h2 := h.S2
  have h3 := h.S3
  have h4 := h.S4
  linarith

private lemma AwEv.sumH3 (h : AwEv N G P σ η ℓ μ Γ u B T) :
    ∑ i, ∑ j, ‖(G * G) i j‖ ^ 3 ≤ ℓ ^ 2 * (N * ℓ ^ 2 / η ^ 2) := by
  have hη2 : 0 < η ^ 2 := pow_pos h.eta 2
  have h2 : ∑ i, ∑ j, ‖(G * G) i j‖ ^ 2 ≤ N * ℓ ^ 2 / η ^ 2 := by
    rw [le_div_iff₀ hη2, mul_comm]; exact h.sumH2
  calc _ ≤ ∑ i, ∑ j, ℓ ^ 2 * ‖(G * G) i j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => by
          calc ‖(G * G) i j‖ ^ 3 = ‖(G * G) i j‖ * ‖(G * G) i j‖ ^ 2 := by ring
            _ ≤ ℓ ^ 2 * ‖(G * G) i j‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (h.H_le i j) (sq_nonneg _)
    _ = ℓ ^ 2 * ∑ i, ∑ j, ‖(G * G) i j‖ ^ 2 := by simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

private lemma AwEv.Q2 (h : AwEv N G P σ η ℓ μ Γ u B T) (b : Bool) :
    ‖∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * awTr2 G i j)‖ ≤
      2 * (ℓ ^ 2 * (2 * N * ℓ * T / η) + u * (N * ℓ ^ 2 / η ^ 2)) +
        2 * (N * (ℓ ^ 2 * (μ * ℓ)) + u * ℓ ^ 2 * (N * (Real.sqrt N * ℓ) / η)) := by
  set D := G - P with hD
  have hη2 : 0 < η ^ 2 := pow_pos h.eta 2
  have hcs : ∀ i j, awCj b ((G * G) i j) = awCj b ((G * G) j i) := fun i j => by
    rw [aw_sq_symm h.symm i j]
  have hsplit : ∀ i j, σ i j * (awCj b ((G * G) i j) * awTr2 G i j) =
      2 * (σ i j * (awCj b ((G * G) i j) * G i j * (G * G) i j)) +
      ((G * G) j j * ((σ i j * P i i) * awCj b ((G * G) i j)) +
        σ i j * (awCj b ((G * G) i j) * D i i * (G * G) j j)) +
      ((G * G) i i * ((σ i j * P j j) * awCj b ((G * G) j i)) +
        σ i j * (awCj b ((G * G) i j) * D j j * (G * G) i i)) := fun i j => by
    rw [← hcs i j]
    simp only [awTr2, hD, Matrix.sub_apply]
    ring
  set SA := ∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * G i j * (G * G) i j) with hSA
  set SB1 := ∑ i, ∑ j, (G * G) j j * ((σ i j * P i i) * awCj b ((G * G) i j)) with hSB1
  set SC1 := ∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * D i i * (G * G) j j) with hSC1
  set SB2 := ∑ i, ∑ j, (G * G) i i * ((σ i j * P j j) * awCj b ((G * G) j i)) with hSB2
  set SC2 := ∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * D j j * (G * G) i i) with hSC2
  have e : ∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * awTr2 G i j) =
      2 * SA + (SB1 + SC1) + (SB2 + SC2) := by
    simp only [hSA, hSB1, hSC1, hSB2, hSC2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
  rw [e]
  -- the four pieces
  have hA : ‖∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * G i j * (G * G) i j)‖ ≤
      ℓ ^ 2 * (2 * N * ℓ * T / η) + u * (N * ℓ ^ 2 / η ^ 2) := by
    refine (aw_norm_sum2 _).trans ?_
    have hpt : ∀ i j, ‖σ i j * (awCj b ((G * G) i j) * G i j * (G * G) i j)‖ ≤
        ℓ ^ 2 * (‖(G * G) i j‖ * ‖P i j‖) + u * ‖(G * G) i j‖ ^ 2 := fun i j => by
      rw [norm_mul, norm_mul, norm_mul, awCj_norm]
      have hG : ‖G i j‖ ≤ ‖P i j‖ + u := by
        have := norm_sub_norm_le (G i j) (P i j)
        linarith [h.tilde i j]
      have := h.sig i j
      have hH := h.H_le i j
      have h0 := norm_nonneg ((G * G) i j)
      have h0' := norm_nonneg (G i j)
      have h0'' := norm_nonneg (P i j)
      calc ‖σ i j‖ * (‖(G * G) i j‖ * ‖G i j‖ * ‖(G * G) i j‖)
          ≤ 1 * (‖(G * G) i j‖ * (‖P i j‖ + u) * ‖(G * G) i j‖) := by gcongr
        _ = ‖(G * G) i j‖ * (‖(G * G) i j‖ * ‖P i j‖) + u * ‖(G * G) i j‖ ^ 2 := by ring
        _ ≤ ℓ ^ 2 * (‖(G * G) i j‖ * ‖P i j‖) + u * ‖(G * G) i j‖ ^ 2 := by gcongr
    have hHP : ∑ i, ∑ j, ‖(G * G) i j‖ * ‖P i j‖ ≤ 2 * N * ℓ * T / η := by
      rw [le_div_iff₀ h.eta, mul_comm]; exact h.sumHP
    have hH2 : ∑ i, ∑ j, ‖(G * G) i j‖ ^ 2 ≤ N * ℓ ^ 2 / η ^ 2 := by
      rw [le_div_iff₀ hη2, mul_comm]; exact h.sumH2
    calc _ ≤ ∑ i, ∑ j, (ℓ ^ 2 * (‖(G * G) i j‖ * ‖P i j‖) + u * ‖(G * G) i j‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
      _ = ℓ ^ 2 * ∑ i, ∑ j, ‖(G * G) i j‖ * ‖P i j‖ + u * ∑ i, ∑ j, ‖(G * G) i j‖ ^ 2 := by
          simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hHP (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hH2 h.u0)
  have hfam : ∀ (t : Fin N → ℂ), awNsq (G *ᵥ t) ≤ μ ^ 2 → awNsq (G *ᵥ star t) ≤ μ ^ 2 →
      ∀ j, ‖∑ i, t i * awCj b ((G * G) i j)‖ ≤ μ * ℓ := fun t ht hts j => by
    cases b
    · simpa [awCj] using h.fam t ht j
    · simpa [awCj] using h.famc t hts j
  have hB1 : ‖∑ i, ∑ j, (G * G) j j * ((σ i j * P i i) * awCj b ((G * G) i j))‖ ≤
      N * (ℓ ^ 2 * (μ * ℓ)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin N, ℓ ^ 2 * (μ * ℓ) := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (h.H_le j j) (hfam _ (h.f1 j) (h.f1s j) j) (norm_nonneg _)
            (sq_nonneg _)
      _ = _ := by simp
  have hB2 : ‖∑ i, ∑ j, (G * G) i i * ((σ i j * P j j) * awCj b ((G * G) j i))‖ ≤
      N * (ℓ ^ 2 * (μ * ℓ)) := by
    simp_rw [← Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : Fin N, ℓ ^ 2 * (μ * ℓ) := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact mul_le_mul (h.H_le i i) (hfam _ (h.f2 i) (h.f2s i) i) (norm_nonneg _)
            (sq_nonneg _)
      _ = _ := by simp
  have hD3 : ∀ (a : Fin N → Fin N → Fin N),
      (∀ i j, ‖D (a i j) (a i j)‖ ≤ u) → ∀ (c : Fin N → Fin N → Fin N × Fin N),
      ‖∑ i, ∑ j, σ i j * (awCj b ((G * G) i j) * D (a i j) (a i j) *
        (G * G) (c i j).1 (c i j).2)‖ ≤ u * ℓ ^ 2 * (N * (Real.sqrt N * ℓ) / η) := by
    intro a ha c
    refine (aw_norm_sum2 _).trans ?_
    have hpt : ∀ i j, ‖σ i j * (awCj b ((G * G) i j) * D (a i j) (a i j) *
        (G * G) (c i j).1 (c i j).2)‖ ≤ u * ℓ ^ 2 * ‖(G * G) i j‖ := fun i j => by
      rw [norm_mul, norm_mul, norm_mul, awCj_norm]
      have := h.sig i j
      have := ha i j
      have := h.H_le (c i j).1 (c i j).2
      have := h.u0
      calc ‖σ i j‖ * (‖(G * G) i j‖ * ‖D (a i j) (a i j)‖ * ‖(G * G) (c i j).1 (c i j).2‖)
          ≤ 1 * (‖(G * G) i j‖ * u * ℓ ^ 2) := by gcongr
        _ = u * ℓ ^ 2 * ‖(G * G) i j‖ := by ring
    calc _ ≤ ∑ i, ∑ j, u * ℓ ^ 2 * ‖(G * G) i j‖ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hpt i j
      _ = u * ℓ ^ 2 * ∑ i, ∑ j, ‖(G * G) i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h.sumH' (mul_nonneg h.u0 (sq_nonneg _))
  have hDt : ∀ a, ‖D a a‖ ≤ u := fun a => by simpa [hD] using h.tilde a a
  have hC1 := hD3 (fun i _ => i) (fun i _ => hDt i) (fun _ j => (j, j))
  have hC2 := hD3 (fun _ j => j) (fun _ j => hDt j) (fun i _ => (i, i))
  simp only at hC1 hC2
  have t1 := norm_add_le (2 * SA + (SB1 + SC1)) (SB2 + SC2)
  have t2 := norm_add_le (2 * SA) (SB1 + SC1)
  have t3 := norm_add_le SB1 SC1
  have t4 := norm_add_le SB2 SC2
  have t5 : ‖(2 : ℂ) * SA‖ = 2 * ‖SA‖ := by rw [norm_mul, Complex.norm_ofNat]
  linarith

end Ev

end Sums

/-! ## The coefficients `f_n` of `F̃^p` -/

section FCoeff

/-- `x^{p−q} y^q ≤ x^p + y^p` for `x, y ≥ 0`, `q ≤ p`. -/
private lemma aw_young {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {p q : ℕ} (hq : q ≤ p) :
    x ^ (p - q) * y ^ q ≤ x ^ p + y ^ p := by
  rcases le_total x y with hxy | hxy
  · calc x ^ (p - q) * y ^ q ≤ y ^ (p - q) * y ^ q :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (pow_nonneg hy _)
      _ = y ^ p := by rw [← pow_add, Nat.sub_add_cancel hq]
      _ ≤ x ^ p + y ^ p := le_add_of_nonneg_left (pow_nonneg hx _)
  · calc x ^ (p - q) * y ^ q ≤ x ^ (p - q) * x ^ q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
      _ = x ^ p := by rw [← pow_add, Nat.sub_add_cancel hq]
      _ ≤ x ^ p + y ^ p := le_add_of_nonneg_right (pow_nonneg hy _)

private lemma aw_card_tuple (p n : ℕ) :
    ((Finset.Nat.antidiagonalTuple p n).card : ℝ) ≤ ((n : ℝ) + 1) ^ p := by
  have hsub : Finset.Nat.antidiagonalTuple p n ⊆
      Fintype.piFinset fun _ : Fin p => Finset.range (n + 1) := by
    intro κ hκ
    rw [Finset.Nat.mem_antidiagonalTuple] at hκ
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro r
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
    omega
  have := Finset.card_le_card hsub
  simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at this
  exact_mod_cast this

private lemma aw_cj_eq (p : ℕ) (r : Fin p) (x : ℂ) :
    (if (r : ℕ) < p / 2 then x else starRingEnd ℂ x) = awCj (!decide ((r : ℕ) < p / 2)) x := by
  by_cases h : (r : ℕ) < p / 2 <;> simp [h, awCj]

/-- `|f_n| ≤ (n+1)^p λ^n (x^p + y^p)` when `|a_0| ≤ x` and `|a_k| ≤ λ^k y` for `1 ≤ k ≤ n`. -/
private lemma aw_fCoeff_le (p n : ℕ) (a : ℕ → ℂ) {x y lam : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hl : 0 ≤ lam) (h0 : ‖a 0‖ ≤ x) (hk : ∀ k, 1 ≤ k → k ≤ n → ‖a k‖ ≤ lam ^ k * y) :
    ‖fCoeff p a n‖ ≤ ((n : ℝ) + 1) ^ p * (lam ^ n * (x ^ p + y ^ p)) := by
  set g : ℕ → ℝ := fun k => if k = 0 then x else y with hg
  have hmax : ∀ k, g k ≤ max x y := fun k => by
    simp only [hg]; split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hg0 : ∀ k, 0 ≤ g k := fun k => by simp only [hg]; split_ifs <;> assumption
  have hM : max x y ^ p ≤ x ^ p + y ^ p := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg hx _)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hy _)
  unfold fCoeff
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _κ ∈ Finset.Nat.antidiagonalTuple p n, lam ^ n * (x ^ p + y ^ p) := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        rw [Finset.Nat.mem_antidiagonalTuple] at hκ
        rw [norm_prod]
        have hle : ∀ r : Fin p, ‖if (r : ℕ) < p / 2 then a (κ r) else starRingEnd ℂ (a (κ r))‖ ≤
            lam ^ κ r * g (κ r) := fun r => by
          have hn : ‖if (r : ℕ) < p / 2 then a (κ r) else starRingEnd ℂ (a (κ r))‖ = ‖a (κ r)‖ := by
            split_ifs <;> simp
          rw [hn]
          have hkr : κ r ≤ n := by
            have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
            omega
          by_cases h0' : κ r = 0
          · simp only [hg, h0', ite_true, pow_zero, one_mul]; exact h0
          · simp only [hg, h0', ite_false]; exact hk _ (Nat.one_le_iff_ne_zero.2 h0') hkr
        calc _ ≤ ∏ r : Fin p, lam ^ κ r * g (κ r) :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hle r
          _ = lam ^ n * ∏ r : Fin p, g (κ r) := by
              rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hκ]
          _ ≤ lam ^ n * ∏ _r : Fin p, max x y :=
              mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun r _ => hg0 _)
                fun r _ => hmax _) (pow_nonneg hl _)
          _ ≤ lam ^ n * (x ^ p + y ^ p) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              exact mul_le_mul_of_nonneg_left hM (pow_nonneg hl _)
    _ = ((Finset.Nat.antidiagonalTuple p n).card : ℝ) * (lam ^ n * (x ^ p + y ^ p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (aw_card_tuple p n)
        (mul_nonneg (pow_nonneg hl _) (add_nonneg (pow_nonneg hx _) (pow_nonneg hy _)))

/-- The order-three coefficient summed against weights `s`: each tuple of `f_3` has `q ∈ {1,2,3}`
nonzero orders; the factors `a_0` do not depend on the entry. -/
private lemma aw_fCoeff3 {ι : Type*} [Fintype ι] (p : ℕ) (s : ι → ℂ) (a : ι → ℕ → ℂ) (a0 : ℂ)
    (h0 : ∀ α, a α 0 = a0) (hs : ∀ α, ‖s α‖ ≤ 1) {L Y : ℝ} (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (h1 : ∀ b : Bool, ‖∑ α, s α * awCj b (a α 3)‖ ≤ L * Y)
    (h2 : ∀ b b' : Bool, ‖∑ α, s α * (awCj b (a α 1) * awCj b' (a α 2))‖ ≤ L * Y ^ 2)
    (h3 : ∑ α, ‖a α 1‖ ^ 3 ≤ L * Y ^ 3) :
    ‖∑ α, s α * fCoeff p (a α) 3‖ ≤ 4 ^ p * (L * (‖a0‖ ^ p + Y ^ p)) := by
  set fl : Fin p → Bool := fun r => !decide ((r : ℕ) < p / 2) with hfl
  have hR : 0 ≤ L * (‖a0‖ ^ p + Y ^ p) := mul_nonneg hL (by positivity)
  have hper : ∀ κ ∈ Finset.Nat.antidiagonalTuple p 3,
      ‖∑ α, s α * ∏ r : Fin p, awCj (fl r) (a α (κ r))‖ ≤ L * (‖a0‖ ^ p + Y ^ p) := by
    intro κ hκ
    rw [Finset.Nat.mem_antidiagonalTuple] at hκ
    set NZ := Finset.univ.filter (fun r : Fin p => κ r ≠ 0) with hNZ
    set Z := Finset.univ.filter (fun r : Fin p => ¬ κ r ≠ 0) with hZ
    have hsplit : ∀ α, ∏ r : Fin p, awCj (fl r) (a α (κ r)) =
        (∏ r ∈ Z, awCj (fl r) a0) * ∏ r ∈ NZ, awCj (fl r) (a α (κ r)) := fun α => by
      rw [← Finset.prod_filter_not_mul_prod_filter Finset.univ (fun r : Fin p => κ r ≠ 0)]
      congr 1
      refine Finset.prod_congr rfl fun r hr => ?_
      have : κ r = 0 := by simpa [hZ] using hr
      rw [this, h0]
    simp_rw [hsplit]
    have hfac : ∑ α, s α * ((∏ r ∈ Z, awCj (fl r) a0) * ∏ r ∈ NZ, awCj (fl r) (a α (κ r))) =
        (∏ r ∈ Z, awCj (fl r) a0) * ∑ α, s α * ∏ r ∈ NZ, awCj (fl r) (a α (κ r)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hfac, norm_mul]
    have hP0 : ‖∏ r ∈ Z, awCj (fl r) a0‖ = ‖a0‖ ^ Z.card := by
      rw [norm_prod]
      simp_rw [awCj_norm]
      rw [Finset.prod_const]
    rw [hP0]
    have hcard : Z.card + NZ.card = p := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun r : Fin p => ¬ κ r ≠ 0)
      simp only [not_not, Finset.card_univ, Fintype.card_fin] at this
      rw [hZ, hNZ]
      simpa [add_comm] using this
    have hsum : ∑ r ∈ NZ, κ r = 3 := by
      rw [hNZ, Finset.sum_filter_ne_zero]; exact hκ
    have hpos : ∀ r ∈ NZ, 1 ≤ κ r := fun r hr => by
      have : κ r ≠ 0 := by simpa [hNZ] using hr
      omega
    have hle3 : NZ.card ≤ 3 := by
      have := Finset.card_nsmul_le_sum NZ (fun r => κ r) 1 hpos
      simp only [smul_eq_mul, mul_one] at this
      omega
    have hge1 : 1 ≤ NZ.card := by
      rcases Nat.eq_zero_or_pos NZ.card with h | h
      · rw [Finset.card_eq_zero] at h
        rw [h, Finset.sum_empty] at hsum
        omega
      · exact h
    have hfin : ∀ q, NZ.card = q → ‖∑ α, s α * ∏ r ∈ NZ, awCj (fl r) (a α (κ r))‖ ≤ L * Y ^ q →
        ‖a0‖ ^ Z.card * ‖∑ α, s α * ∏ r ∈ NZ, awCj (fl r) (a α (κ r))‖ ≤
          L * (‖a0‖ ^ p + Y ^ p) := fun q hq hb => by
      have hZc : Z.card = p - q := by omega
      rw [hZc]
      calc ‖a0‖ ^ (p - q) * ‖∑ α, s α * ∏ r ∈ NZ, awCj (fl r) (a α (κ r))‖
          ≤ ‖a0‖ ^ (p - q) * (L * Y ^ q) := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = L * (‖a0‖ ^ (p - q) * Y ^ q) := by ring
        _ ≤ L * (‖a0‖ ^ p + Y ^ p) :=
            mul_le_mul_of_nonneg_left (aw_young (norm_nonneg _) hY (by omega)) hL
    interval_cases hc : NZ.card
    · obtain ⟨r0, hr0⟩ := Finset.card_eq_one.1 hc
      refine hfin 1 rfl ?_
      rw [hr0] at hsum ⊢
      simp only [Finset.sum_singleton] at hsum
      simp only [Finset.prod_singleton, hsum, pow_one]
      exact h1 _
    · obtain ⟨r1, r2, hne, hr⟩ := Finset.card_eq_two.1 hc
      refine hfin 2 rfl ?_
      have h1m : r1 ∈ NZ := by rw [hr]; simp
      have h2m : r2 ∈ NZ := by rw [hr]; simp
      have hk1 := hpos r1 h1m
      have hk2 := hpos r2 h2m
      rw [hr] at hsum ⊢
      rw [Finset.sum_pair hne] at hsum
      simp only [Finset.prod_pair hne]
      rcases (show (κ r1 = 1 ∧ κ r2 = 2) ∨ (κ r1 = 2 ∧ κ r2 = 1) by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact h2 _ _
      · rw [e1, e2]
        have := h2 (fl r2) (fl r1)
        simpa [mul_comm] using this
    · obtain ⟨r1, r2, r3, h12, h13, h23, hr⟩ := Finset.card_eq_three.1 hc
      refine hfin 3 rfl ?_
      have h1m : r1 ∈ NZ := by rw [hr]; simp
      have h2m : r2 ∈ NZ := by rw [hr]; simp
      have h3m : r3 ∈ NZ := by rw [hr]; simp
      have hk1 := hpos r1 h1m
      have hk2 := hpos r2 h2m
      have hk3 := hpos r3 h3m
      rw [hr] at hsum ⊢
      have hn1 : r1 ∉ ({r2, r3} : Finset (Fin p)) := by simp [h12, h13]
      have hn2 : r2 ∉ ({r3} : Finset (Fin p)) := by simp [h23]
      rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_singleton] at hsum
      have e1 : κ r1 = 1 := by omega
      have e2 : κ r2 = 1 := by omega
      have e3 : κ r3 = 1 := by omega
      simp only [Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_singleton, e1, e2, e3]
      refine (norm_sum_le _ _).trans (le_trans ?_ h3)
      refine Finset.sum_le_sum fun α _ => ?_
      rw [norm_mul, norm_mul, norm_mul, awCj_norm, awCj_norm, awCj_norm]
      have := hs α
      calc ‖s α‖ * (‖a α 1‖ * (‖a α 1‖ * ‖a α 1‖)) ≤ 1 * (‖a α 1‖ * (‖a α 1‖ * ‖a α 1‖)) := by
            gcongr
        _ = ‖a α 1‖ ^ 3 := by ring
  have e : ∑ α, s α * fCoeff p (a α) 3 =
      ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ α, s α * ∏ r : Fin p, awCj (fl r) (a α (κ r)) := by
    unfold fCoeff
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun α _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun r _ => aw_cj_eq p r _
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _κ ∈ Finset.Nat.antidiagonalTuple p 3, L * (‖a0‖ ^ p + Y ^ p) :=
        Finset.sum_le_sum hper
    _ = ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) * (L * (‖a0‖ ^ p + Y ^ p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((3 : ℝ) + 1) ^ p * (L * (‖a0‖ ^ p + Y ^ p)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast aw_card_tuple p 3) hR
    _ = 4 ^ p * (L * (‖a0‖ ^ p + Y ^ p)) := by norm_num

end FCoeff

/-! ## Bounds at a fixed matrix -/

section Fixed

variable {N : ℕ}

private lemma aw_col_eq (M : Matrix (Fin N) (Fin N) ℂ) (a : Fin N) :
    M *ᵥ cvec (Pi.single a (1 : ℝ)) = fun c => M c a := by
  funext c
  simp [Matrix.mulVec, dotProduct, cvec, Pi.single_apply, apply_ite (fun x : ℝ => (x : ℂ)),
    mul_ite]

private lemma aw_testNorm_single (a : Fin N) : testNorm (Pi.single a (1 : ℝ)) = 1 := by
  rw [testNorm]
  have : ∑ c, (Pi.single a (1 : ℝ) : Fin N → ℝ) c ^ 2 = 1 := by
    simp [Pi.single_apply]
  rw [this, Real.sqrt_one]

private lemma aw_testBilin_single (M : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    testBilin (Pi.single a (1 : ℝ)) M (Pi.single b (1 : ℝ)) = M a b := by
  simp [testBilin, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (fun x : ℝ => (x : ℂ)),
    mul_ite, ite_mul]

private lemma aw_testBilin_single_left (M : Matrix (Fin N) (Fin N) ℂ) (a : Fin N)
    (v : Fin N → ℝ) : testBilin (Pi.single a (1 : ℝ)) M v = (M *ᵥ cvec v) a := by
  simp [testBilin, dotProduct, Pi.single_apply, apply_ite (fun x : ℝ => (x : ℂ)), ite_mul]

private lemma aw_testBilin_sub (M M' : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℝ) :
    testBilin v (M - M') w = testBilin v M w - testBilin v M' w := by
  simp [testBilin, Matrix.sub_mulVec, dotProduct_sub]

private lemma aw_nsq_single (a : Fin N) : awNsq (cvec (Pi.single a (1 : ℝ))) = 1 := by
  simp [awNsq, cvec, Pi.single_apply]

/-- `|G_{ab}| ≤ |G e_b|`. -/
private lemma aw_entry_le_col (M : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    ‖M a b‖ ^ 2 ≤ awNsq (fun c => M c b) :=
  Finset.single_le_sum (f := fun c => ‖M c b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- Deterministic bounds: `|G e_a|² ≤ η⁻²`, `|G_{ab}| ≤ η⁻¹`, `|(G²)_{ab}| ≤ η⁻²`. -/
private lemma aw_det_col {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    {z : ℂ} (hz : 0 < z.im) (a : Fin N) :
    awNsq (fun c => GW A Wm z c a) ≤ (z.im⁻¹) ^ 2 := by
  have h := aw_GW_op hA hW hz (cvec (Pi.single a (1 : ℝ)))
  rw [aw_col_eq, aw_nsq_single] at h
  rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos hz 2)]
  linarith


/-- `|(G²)_{ab}| ≤ L²` when `G` is symmetric with columns bounded by `L`. -/
private lemma aw_H_le_of_col {G : Matrix (Fin N) (Fin N) ℂ} (hG : ∀ a b, G b a = G a b) {L : ℝ}
    (hL : 0 ≤ L) (hc : ∀ a, awNsq (fun c => G c a) ≤ L ^ 2) (a b : Fin N) :
    ‖(G * G) a b‖ ≤ L ^ 2 := by
  have e : (G * G) a b = ∑ c, G c a * G c b := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [hG c a]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  have := aw_cs (fun c => ‖G c a‖) (fun c => ‖G c b‖) hL hL (hc a) (hc b)
  simpa [sq] using this

private lemma aw_entry_le {G : Matrix (Fin N) (Fin N) ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ a, awNsq (fun c => G c a) ≤ L ^ 2) (a b : Fin N) : ‖G a b‖ ≤ L :=
  aw_le_of_sq hL ((aw_entry_le_col G a b).trans (hc b))

private lemma aw_norm_mNW_le {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) {z : ℂ} {L : ℝ}
    (hL : ∀ a, ‖GW A Wm z a a‖ ≤ L) : ‖mNW A Wm z‖ ≤ L := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold mNW
  rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
  calc (N : ℝ)⁻¹ * ‖∑ a, Matrix.diag (GW A Wm z) a‖ ≤ (N : ℝ)⁻¹ * ∑ _a : Fin N, L :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hL a))
          (inv_nonneg.2 hNr.le)
    _ = L := by simp; field_simp

/-- Deterministic bounds on the coefficients: `|a_0| ≤ η⁻¹ + 1`, `|a_{k+1}| ≤ (4η⁻¹)^{k+1} η⁻¹`. -/
private lemma aw_det_coeff {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    ‖avgCoeffW A Wm z i j 0‖ ≤ z.im⁻¹ + 1 ∧
      ∀ k, 1 ≤ k → ‖avgCoeffW A Wm z i j k‖ ≤ (4 * z.im⁻¹) ^ k * z.im⁻¹ := by
  have hη : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  have hcol := aw_det_col hA hW hz (Wm := Wm)
  have hent := aw_entry_le hη hcol
  have hH := aw_H_le_of_col (aw_GW_symm hA hW z) hη hcol
  constructor
  · rw [aw_avgCoeff_zero]
    refine (norm_sub_le _ _).trans (add_le_add (aw_norm_mNW_le hN fun a => hent a a) ?_)
    exact (norm_mW_lt_one hN _ hz).le
  · intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (aw_avgCoeff_le hη hent hH i j k').trans ?_
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h0 : 0 ≤ 4 * (4 * z.im⁻¹) ^ k' * z.im⁻¹ ^ 2 := by positivity
    calc 4 * (4 * z.im⁻¹) ^ k' * z.im⁻¹ ^ 2 / N ≤ 4 * (4 * z.im⁻¹) ^ k' * z.im⁻¹ ^ 2 :=
          div_le_self h0 hNr
      _ = (4 * z.im⁻¹) ^ (k' + 1) * z.im⁻¹ := by ring

private lemma aw_det_fCoeff {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (p n : ℕ) :
    ‖fCoeff p (avgCoeffW A Wm z i j) n‖ ≤
      ((n : ℝ) + 1) ^ p * ((4 * z.im⁻¹) ^ n * ((z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p)) := by
  have hη : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  obtain ⟨h0, hk⟩ := aw_det_coeff hN hA hW hz i j (Wm := Wm)
  exact aw_fCoeff_le p n _ (by positivity) hη (by positivity) h0 fun k hk1 _ => hk k hk1

private lemma aw_FtW_le {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) : FtW A Wm z ≤ z.im⁻¹ + 1 := by
  have := (aw_det_coeff hN hA hW hz (Wm := Wm) ⟨0, by omega⟩ ⟨0, by omega⟩).1
  rwa [aw_avgCoeff_zero] at this

/-- Facts on `Ψ^W`: `(Nη)⁻¹ ≤ Ψ`, `Im m/(Nη) ≤ Ψ²`, and `Ψ ≤ 2` when `Nη ≥ 1`. -/
private lemma aw_psi {a : Fin N → ℝ} (hN : 1 ≤ N) {z : ℂ} (hz : 0 < z.im) :
    1 / (N * z.im) ≤ PsiW a z ∧ (mW a z).im / (N * z.im) ≤ PsiW a z ^ 2 ∧
      (1 ≤ N * z.im → PsiW a z ≤ 2) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNη : 0 < (N : ℝ) * z.im := by positivity
  have hm := (mW_spec hN a hz).1
  have hm1 : (mW a z).im < 1 := lt_of_le_of_lt (Complex.im_le_norm _) (norm_mW_lt_one hN a hz)
  have hq : 0 ≤ (mW a z).im / (N * z.im) := by positivity
  have hs := Real.sqrt_nonneg ((mW a z).im / (N * z.im))
  refine ⟨?_, ?_, ?_⟩
  · unfold PsiW; linarith
  · unfold PsiW
    have h1 := Real.sq_sqrt hq
    have h2 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
    nlinarith
  · intro h1
    unfold PsiW
    have h2 : 1 / ((N : ℝ) * z.im) ≤ 1 := by rw [div_le_one hNη]; exact h1
    have h3 : (mW a z).im / (N * z.im) ≤ 1 := by
      rw [div_le_one hNη]; linarith
    have h4 : Real.sqrt ((mW a z).im / (N * z.im)) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact h3
    linarith

/-- On the event, the anisotropic bound at `(v, v)` gives `|G v|² ≤ c₁ e N Ψ² |v|²`. -/
private lemma aw_col_event {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im) {κ e : ℝ} (hκ : 0 < κ)
    (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) (v : Fin N → ℝ)
    (hv : ‖testBilin v (GW A Wm z - piW A z) v‖ ≤ e * PsiW (specOf A) z * testNorm v ^ 2) :
    awNsq (GW A Wm z *ᵥ cvec v) ≤
      (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) * e * N * PsiW (specOf A) z ^ 2 * testNorm v ^ 2 := by
  obtain ⟨hp1, hp2, -⟩ := aw_psi (a := specOf A) hN hz
  have hmpos : 0 < (mW (specOf A) z).im := (mW_spec hN (specOf A) hz).1
  set Ψ := PsiW (specOf A) z with hΨ
  set m := mW (specOf A) z with hm
  set η := z.im with hη
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNη : 0 < (N : ℝ) * η := by positivity
  have hΨ1 : 1 ≤ N * η * Ψ := by rw [div_le_iff₀ hNη] at hp1; linarith
  have hΨ2 : m.im ≤ N * η * Ψ ^ 2 := by rw [div_le_iff₀ hNη] at hp2; linarith
  have hT : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
  have hv2 := sq_nonneg (testNorm v)
  have hPn : awNsq (piW A z *ᵥ cvec v) ≤ 2 * τ⁻¹ ^ 2 * testNorm v ^ 2 :=
    aw_nsq_le_of_bilin v fun w => norm_piW_le hτ hA hS hzS w v
  have hW1 := aw_GW_ward hA hW hz v (Wm := Wm)
  have hP1 := aw_piW_ward hN hA hz v
  have hsplit : (testBilin v (GW A Wm z) v).im =
      (testBilin v (piW A z) v).im + (testBilin v (GW A Wm z - piW A z) v).im := by
    rw [aw_testBilin_sub]; simp
  have hD := (Complex.im_le_norm _).trans hv
  have hwim : (m + z).im = m.im + η := by simp [hη]
  rw [hwim] at hP1
  have hG0 := awNsq_nonneg (GW A Wm z *ᵥ cvec v)
  have hP0 := awNsq_nonneg (piW A z *ᵥ cvec v)
  -- `η |Gv|² ≤ (Im m + η) 2T² |v|² + e Ψ |v|²`
  have key : η * awNsq (GW A Wm z *ᵥ cvec v) ≤
      (m.im + η) * (2 * τ⁻¹ ^ 2 * testNorm v ^ 2) + e * Ψ * testNorm v ^ 2 := by
    rw [← hW1, hsplit, hP1]
    have := mul_le_mul_of_nonneg_left hPn (by linarith : 0 ≤ m.im + η)
    linarith
  have hηκ : η ≤ κ⁻¹ * m.im := by
    rw [le_inv_mul_iff₀ hκ]; linarith
  have hb1 : (m.im + η) ≤ (1 + κ⁻¹) * (N * η * Ψ ^ 2) := by nlinarith [inv_pos.2 hκ]
  have hb2 : e * Ψ ≤ e * (N * η * Ψ ^ 2) := by
    have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hp1
    have h1 : Ψ ≤ N * η * Ψ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hΨ1 hΨ0
      calc Ψ = 1 * Ψ := (one_mul _).symm
        _ ≤ N * η * Ψ * Ψ := this
        _ = N * η * Ψ ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have hc : (m.im + η) * (2 * τ⁻¹ ^ 2 * testNorm v ^ 2) + e * Ψ * testNorm v ^ 2 ≤
      η * ((2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) * e * N * Ψ ^ 2 * testNorm v ^ 2) := by
    have h1 : (m.im + η) * (2 * τ⁻¹ ^ 2 * testNorm v ^ 2) ≤
        (1 + κ⁻¹) * (N * η * Ψ ^ 2) * (2 * τ⁻¹ ^ 2 * testNorm v ^ 2) :=
      mul_le_mul_of_nonneg_right hb1 (by positivity)
    have h2 : e * Ψ * testNorm v ^ 2 ≤ e * (N * η * Ψ ^ 2) * testNorm v ^ 2 :=
      mul_le_mul_of_nonneg_right hb2 hv2
    have h3 : 0 ≤ (e - 1) * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹)) * (N * η * Ψ ^ 2) * testNorm v ^ 2 := by
      have := inv_pos.2 hκ
      have : 0 ≤ e - 1 := by linarith
      positivity
    nlinarith
  have := key.trans hc
  exact le_of_mul_le_mul_left this hz

private lemma aw_nsq_add_I (x y : Fin N → ℂ) :
    awNsq (x + Complex.I • y) ≤ 2 * (awNsq x + awNsq y) := by
  unfold awNsq
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := norm_add_le (x c) (Complex.I * y c)
  rw [norm_mul, Complex.norm_I, one_mul] at h
  have h0 := norm_nonneg (x c + Complex.I * y c)
  nlinarith [sq_nonneg (‖x c‖ - ‖y c‖), norm_nonneg (x c), norm_nonneg (y c)]

private lemma aw_nsq_neg (x : Fin N → ℂ) : awNsq (-x) = awNsq x := by
  simp [awNsq]

private lemma aw_parts (t : Fin N → ℂ) :
    t = cvec (fun i => (t i).re) + Complex.I • cvec (fun i => (t i).im) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cvec]
  rw [mul_comm]
  exact (Complex.re_add_im (t i)).symm

private lemma aw_parts_star (t : Fin N → ℂ) :
    star t = cvec (fun i => (t i).re) + Complex.I • (-cvec (fun i => (t i).im)) := by
  funext i
  simp only [Pi.star_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, cvec]
  apply Complex.ext <;> simp

private lemma aw_parts_norm (t : Fin N → ℂ) :
    testNorm (fun i => (t i).re) ^ 2 + testNorm (fun i => (t i).im) ^ 2 = awNsq t := by
  rw [aw_testNorm_sq, aw_testNorm_sq, awNsq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private lemma aw_nsq_le_of_entry (t : Fin N → ℂ) {T : ℝ} (ht : ∀ i, ‖t i‖ ≤ T) :
    awNsq t ≤ N * T ^ 2 := by
  unfold awNsq
  calc _ ≤ ∑ _c : Fin N, T ^ 2 := Finset.sum_le_sum fun c _ =>
        pow_le_pow_left₀ (norm_nonneg _) (ht c) 2
    _ = _ := by simp

/-- The bounds `|G t|, |G t̄| ≤ 2 ℓ T √N` and `|(G t)_j| ≤ 2 (T + u) T √N` for a complex vector
`t` with `|t_i| ≤ T`, from the anisotropic bounds at its real and imaginary parts. -/
private lemma aw_vec_bounds {G P : Matrix (Fin N) (Fin N) ℂ} (t : Fin N → ℂ) {T u ℓ : ℝ}
    (hT : 0 ≤ T) (hu : 0 ≤ u) (ht : ∀ i, ‖t i‖ ≤ T) (j : Fin N)
    (hcol : ∀ v : Fin N → ℝ, ‖testBilin v (G - P) v‖ ≤ u * testNorm v ^ 2 →
      awNsq (G *ᵥ cvec v) ≤ ℓ ^ 2 * testNorm v ^ 2)
    (hP : ∀ v : Fin N → ℝ, ‖testBilin (Pi.single j 1) P v‖ ≤ T * testNorm v)
    (hRR : ‖testBilin (fun i => (t i).re) (G - P) (fun i => (t i).re)‖ ≤
      u * testNorm (fun i => (t i).re) ^ 2)
    (hII : ‖testBilin (fun i => (t i).im) (G - P) (fun i => (t i).im)‖ ≤
      u * testNorm (fun i => (t i).im) ^ 2)
    (hjR : ‖testBilin (Pi.single j 1) (G - P) (fun i => (t i).re)‖ ≤
      u * testNorm (fun i => (t i).re))
    (hjI : ‖testBilin (Pi.single j 1) (G - P) (fun i => (t i).im)‖ ≤
      u * testNorm (fun i => (t i).im)) :
    awNsq (G *ᵥ t) ≤ (2 * ℓ * T * Real.sqrt N) ^ 2 ∧
      awNsq (G *ᵥ star t) ≤ (2 * ℓ * T * Real.sqrt N) ^ 2 ∧
      ‖(G *ᵥ t) j‖ ≤ 2 * (T + u) * T * Real.sqrt N := by
  set tR : Fin N → ℝ := fun i => (t i).re with htR
  set tI : Fin N → ℝ := fun i => (t i).im with htI
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpn := aw_parts_norm t
  rw [← htR, ← htI] at hpn
  have hnt := aw_nsq_le_of_entry t ht
  have hR2 : testNorm tR ^ 2 ≤ (T * Real.sqrt N) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0]; nlinarith [sq_nonneg (testNorm tI)]
  have hI2 : testNorm tI ^ 2 ≤ (T * Real.sqrt N) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0]; nlinarith [sq_nonneg (testNorm tR)]
  have hTs : 0 ≤ T * Real.sqrt N := mul_nonneg hT (Real.sqrt_nonneg _)
  have hR1 : testNorm tR ≤ T * Real.sqrt N := aw_le_of_sq hTs hR2
  have hI1 : testNorm tI ≤ T * Real.sqrt N := aw_le_of_sq hTs hI2
  have hGR := hcol tR hRR
  have hGI := hcol tI hII
  have hsum : awNsq (G *ᵥ cvec tR) + awNsq (G *ᵥ cvec tI) ≤ ℓ ^ 2 * (N * T ^ 2) := by
    have := add_le_add hGR hGI
    rw [← mul_add, hpn] at this
    exact this.trans (mul_le_mul_of_nonneg_left hnt (sq_nonneg _))
  have hfin : 2 * (ℓ ^ 2 * (N * T ^ 2)) ≤ (2 * ℓ * T * Real.sqrt N) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hN0]
    nlinarith [sq_nonneg ℓ, sq_nonneg T]
  refine ⟨?_, ?_, ?_⟩
  · have e : G *ᵥ t = G *ᵥ cvec tR + Complex.I • (G *ᵥ cvec tI) := by
      conv_lhs => rw [aw_parts t]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [e]
    exact (aw_nsq_add_I _ _).trans (le_trans (by linarith) hfin)
  · have e : G *ᵥ star t = G *ᵥ cvec tR + Complex.I • (-(G *ᵥ cvec tI)) := by
      rw [aw_parts_star t, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg]
    rw [e]
    refine (aw_nsq_add_I _ _).trans ?_
    rw [aw_nsq_neg]
    exact le_trans (by linarith) hfin
  · have e : (G *ᵥ t) j = testBilin (Pi.single j 1) G tR +
        Complex.I * testBilin (Pi.single j 1) G tI := by
      rw [aw_testBilin_single_left, aw_testBilin_single_left]
      conv_lhs => rw [aw_parts t]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    have hb : ∀ v : Fin N → ℝ, ‖testBilin v (G - P) v‖ ≤ u * testNorm v ^ 2 →
        ‖testBilin (Pi.single j 1) (G - P) v‖ ≤ u * testNorm v →
        ‖testBilin (Pi.single j 1) G v‖ ≤ (T + u) * testNorm v := fun v _ h2 => by
      have e2 : testBilin (Pi.single j 1) G v = testBilin (Pi.single j 1) P v +
          testBilin (Pi.single j 1) (G - P) v := by rw [aw_testBilin_sub]; ring
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      have := hP v
      linarith
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have h1 := hb tR hRR hjR
    have h2 := hb tI hII hjI
    have hTu : 0 ≤ T + u := by linarith
    have := mul_le_mul_of_nonneg_left hR1 hTu
    have := mul_le_mul_of_nonneg_left hI1 hTu
    nlinarith

/-- `σ_{ij} = s_{(i,j)}` for `i < j`, and `0` otherwise. -/
private def awSig (s : UpperIdx N → ℂ) (i j : Fin N) : ℂ :=
  if h : i < j then s ⟨(i, j), h.le⟩ else 0

private lemma awSig_norm {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) (i j : Fin N) :
    ‖awSig s i j‖ ≤ 1 := by
  unfold awSig
  split_ifs
  · exact hs _
  · simp

/-- The test vectors `(σ_{ij} Π_{ii})_i` (`b₂ = true`, index `j`) and `(σ_{ji} Π_{ii})_i`
(`b₂ = false`, index `j`), with `σ` or `σ̄` according to `b₁`. -/
private def awT (s : UpperIdx N → ℂ) (P : Matrix (Fin N) (Fin N) ℂ) (b1 b2 : Bool) (j : Fin N) :
    Fin N → ℂ :=
  fun i => if b2 then awCj b1 (awSig s i j) * P i i else awCj b1 (awSig s j i) * P i i

/-- The `9N` real test vectors: the unit vectors and the real and imaginary parts of `awT`. -/
private def awVec (s : UpperIdx N → ℂ) (P : Matrix (Fin N) (Fin N) ℂ) :
    Fin N ⊕ (Bool × Bool × Bool × Fin N) → Fin N → ℝ
  | Sum.inl a => Pi.single a 1
  | Sum.inr (b1, b2, b3, j) =>
      fun i => if b3 then (awT s P b1 b2 j i).re else (awT s P b1 b2 j i).im

private lemma awT_norm {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) {P : Matrix (Fin N) (Fin N) ℂ}
    {T : ℝ} (hP : ∀ a b, ‖P a b‖ ≤ T) (b1 b2 : Bool) (j i : Fin N) : ‖awT s P b1 b2 j i‖ ≤ T := by
  have hT : 0 ≤ T := (norm_nonneg _).trans (hP i i)
  unfold awT
  split_ifs
  · rw [norm_mul, awCj_norm]
    calc ‖awSig s i j‖ * ‖P i i‖ ≤ 1 * T :=
          mul_le_mul (awSig_norm hs i j) (hP i i) (norm_nonneg _) zero_le_one
      _ = T := one_mul T
  · rw [norm_mul, awCj_norm]
    calc ‖awSig s j i‖ * ‖P i i‖ ≤ 1 * T :=
          mul_le_mul (awSig_norm hs j i) (hP i i) (norm_nonneg _) zero_le_one
      _ = T := one_mul T

/-- The event at a fixed matrix gives the hypotheses `AwEv` for the weights `σ` and `σ̄`. -/
private lemma aw_mkEv {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im) {κ e : ℝ} (hκ : 0 < κ)
    (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) {s : UpperIdx N → ℂ}
    (hs : ∀ α, ‖s α‖ ≤ 1)
    (hE : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      e * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) * testNorm (awVec s (piW A z) l))
    (b : Bool) :
    AwEv N (GW A Wm z) (piW A z) (fun i j => awCj b (awSig s i j)) z.im
      (Real.sqrt ((2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) * e * N * PsiW (specOf A) z ^ 2))
      (2 * Real.sqrt ((2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) * e * N * PsiW (specOf A) z ^ 2) * τ⁻¹ *
        Real.sqrt N)
      (2 * (τ⁻¹ + e * PsiW (specOf A) z) * τ⁻¹ * Real.sqrt N) (e * PsiW (specOf A) z)
      (τ⁻¹ + e * PsiW (specOf A) z) τ⁻¹ := by
  set G := GW A Wm z with hG
  set P := piW A z with hP
  set Ψ := PsiW (specOf A) z with hΨ
  set c₁ := 2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1 with hc₁
  set ℓ := Real.sqrt (c₁ * e * N * Ψ ^ 2) with hℓ
  have hT : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) (aw_psi (a := specOf A) hN hz).1
  have hu : 0 ≤ e * Ψ := mul_nonneg (by linarith) hΨ0
  have hc0 : 0 ≤ c₁ * e * N * Ψ ^ 2 := by
    have := inv_pos.2 hκ
    have : (0 : ℝ) ≤ e := by linarith
    positivity
  have hℓ2 : ℓ ^ 2 = c₁ * e * N * Ψ ^ 2 := Real.sq_sqrt hc0
  have hℓ0 : 0 ≤ ℓ := Real.sqrt_nonneg _
  have hcolv : ∀ v : Fin N → ℝ, ‖testBilin v (G - P) v‖ ≤ e * Ψ * testNorm v ^ 2 →
      awNsq (G *ᵥ cvec v) ≤ ℓ ^ 2 * testNorm v ^ 2 := fun v hv => by
    rw [hℓ2]
    exact aw_col_event hN hA hW hτ hS hzS hz hκ hIm he v hv
  have hEv : ∀ k, ‖testBilin (awVec s P k) (G - P) (awVec s P k)‖ ≤
      e * Ψ * testNorm (awVec s P k) ^ 2 := fun k => by
    have := hE k k; rw [sq]; linarith
  have hEj : ∀ j k, ‖testBilin (Pi.single j 1) (G - P) (awVec s P k)‖ ≤
      e * Ψ * testNorm (awVec s P k) := fun j k => by
    have := hE (Sum.inl j) k
    simp only [awVec, aw_testNorm_single, mul_one] at this
    exact this
  have hPe : ∀ a b, ‖P a b‖ ≤ τ⁻¹ := fun a b => by
    have := norm_piW_le hτ hA hS hzS (Pi.single a 1) (Pi.single b 1)
    rwa [aw_testBilin_single, aw_testNorm_single, aw_testNorm_single, mul_one, mul_one] at this
  have hPj : ∀ j (v : Fin N → ℝ), ‖testBilin (Pi.single j 1) P v‖ ≤ τ⁻¹ * testNorm v :=
    fun j v => by
      have := norm_piW_le hτ hA hS hzS (Pi.single j 1) v
      rwa [aw_testNorm_single, mul_one] at this
  have hfam : ∀ (b2 : Bool) (j : Fin N),
      awNsq (G *ᵥ awT s P b b2 j) ≤ (2 * ℓ * τ⁻¹ * Real.sqrt N) ^ 2 ∧
      awNsq (G *ᵥ star (awT s P b b2 j)) ≤ (2 * ℓ * τ⁻¹ * Real.sqrt N) ^ 2 ∧
      ‖(G *ᵥ awT s P b b2 j) j‖ ≤ 2 * (τ⁻¹ + e * Ψ) * τ⁻¹ * Real.sqrt N := fun b2 j =>
    aw_vec_bounds (G := G) (P := P) (awT s P b b2 j) hT hu (awT_norm hs hPe b b2 j) j hcolv
      (hPj j) (hEv (Sum.inr (b, b2, true, j))) (hEv (Sum.inr (b, b2, false, j)))
      (hEj j (Sum.inr (b, b2, true, j))) (hEj j (Sum.inr (b, b2, false, j)))
  have h1 : ∀ j, (fun i => awCj b (awSig s i j) * P i i) = awT s P b true j := fun j => by
    funext i; simp [awT]
  have h2 : ∀ i, (fun j => awCj b (awSig s i j) * P j j) = awT s P b false i := fun i => by
    funext j; simp [awT]
  refine
    { eta := hz
      ell := hℓ0
      mu := by positivity
      gam := by positivity
      u0 := hu
      B0 := by positivity
      T0 := hT
      symm := aw_GW_symm hA hW z
      op := aw_GW_op hA hW hz
      col := fun a => ?_
      tilde := fun a b' => ?_
      bdd := fun a b' => ?_
      piB := hPe
      piCol := fun a => ?_
      sig := fun i j => by rw [awCj_norm]; exact awSig_norm hs i j
      f1 := fun j => by rw [h1]; exact (hfam true j).1
      f1s := fun j => by rw [h1]; exact (hfam true j).2.1
      f2 := fun i => by rw [h2]; exact (hfam false i).1
      f2s := fun i => by rw [h2]; exact (hfam false i).2.1
      e1 := fun j => by rw [h1]; exact (hfam true j).2.2
      e2 := fun i => by rw [h2]; exact (hfam false i).2.2 }
  · have := hcolv (Pi.single a 1) (by
      have := hEv (Sum.inl a); simpa [awVec] using this)
    rwa [aw_col_eq, aw_testNorm_single, one_pow, mul_one] at this
  · have := hE (Sum.inl a) (Sum.inl b')
    simp only [awVec, aw_testBilin_single, aw_testNorm_single, mul_one] at this
    simpa [Matrix.sub_apply] using this
  · have h3 := hE (Sum.inl a) (Sum.inl b')
    simp only [awVec, aw_testBilin_single, aw_testNorm_single, mul_one, Matrix.sub_apply] at h3
    have := norm_sub_norm_le (G a b') (P a b')
    linarith [hPe a b']
  · have := aw_nsq_le_of_bilin (M := P) (T := τ⁻¹) (Pi.single a 1) fun w =>
      norm_piW_le hτ hA hS hzS w (Pi.single a 1)
    rwa [aw_col_eq, aw_testNorm_single, one_pow, mul_one] at this
end Fixed

/-! ## Scalar inequalities for the order-three sums -/

section Scalar

/-- The scalar facts used for `n = 3` under (b): `ℓ² = c₁ e N Ψ²`, `u = eΨ ≤ 1`, `e⁴ ≤ D`,
`1 ≤ N η Ψ`, `N Ψ² ≤ √N β⁴` (from `Ψ ≤ N^{−1/4−c₀}` with `β = N^{−c₀/2}`). -/
private structure AwSc (Nr sN η Ψ e T c₁ D β ℓ : ℝ) : Prop where
  sN0 : 1 ≤ sN
  sN2 : sN ^ 2 = Nr
  eta : 0 < η
  psi : 0 ≤ Ψ
  e1 : 1 ≤ e
  T1 : 1 ≤ T
  c1 : 1 ≤ c₁
  eD : e ^ 4 ≤ D
  β0 : 0 < β
  β1 : β ≤ 1
  ell : 0 ≤ ℓ
  ell2 : ℓ ^ 2 = c₁ * e * Nr * Ψ ^ 2
  u1 : e * Ψ ≤ 1
  etaPsi : 1 ≤ Nr * η * Ψ
  small : Nr * Ψ ^ 2 ≤ sN * β ^ 4

section ScFacts

variable {Nr sN η Ψ e T c₁ D β ℓ : ℝ}

private lemma AwSc.N1 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) : 1 ≤ Nr := by
  have := h.sN0; rw [← h.sN2]; nlinarith

private lemma AwSc.eD1 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) {k : ℕ} (hk : k ≤ 4) : e ^ k ≤ D :=
  (pow_le_pow_right₀ h.e1 hk).trans h.eD

private lemma AwSc.eDb (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) {k : ℕ} (hk : k ≤ 4) :
    e ^ k * β ^ 4 ≤ D :=
  (mul_le_of_le_one_right (pow_nonneg (by linarith [h.e1]) k)
    (pow_le_one₀ h.β0.le h.β1)).trans (h.eD1 hk)

private lemma AwSc.D0 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) : 1 ≤ D :=
  (one_le_pow₀ h.e1).trans h.eD

/-- `N Ψ⁴ ≤ β⁸`. -/
private lemma AwSc.NPsi4 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) : Nr * Ψ ^ 4 ≤ β ^ 8 := by
  have hN := h.N1
  have h1 : (Nr * Ψ ^ 2) ^ 2 ≤ (sN * β ^ 4) ^ 2 :=
    pow_le_pow_left₀ (by have := h.psi; positivity) h.small 2
  have e1 : (sN * β ^ 4) ^ 2 = Nr * β ^ 8 := by rw [mul_pow, h.sN2]; ring
  rw [e1] at h1
  have : Nr * (Nr * Ψ ^ 4) ≤ Nr * β ^ 8 := by nlinarith
  exact le_of_mul_le_mul_left this (by linarith)

/-- `1/η ≤ N Ψ`. -/
private lemma AwSc.inv_eta (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) : η⁻¹ ≤ Nr * Ψ := by
  have := h.etaPsi
  have hη := h.eta
  rw [inv_le_iff_one_le_mul₀ hη]
  linarith

/-- `ℓ⁴ ≤ c₁² e² N √N Ψ² β⁴`. -/
private lemma AwSc.ell4 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) :
    ℓ ^ 4 ≤ c₁ ^ 2 * e ^ 2 * (Nr * sN) * Ψ ^ 2 * β ^ 4 := by
  have e1 : ℓ ^ 4 = (c₁ * e) ^ 2 * Nr * Ψ ^ 2 * (Nr * Ψ ^ 2) := by
    rw [show ℓ ^ 4 = (ℓ ^ 2) ^ 2 by ring, h.ell2]; ring
  rw [e1]
  have hc : 0 ≤ (c₁ * e) ^ 2 * Nr * Ψ ^ 2 := by have := h.N1; positivity
  calc _ ≤ (c₁ * e) ^ 2 * Nr * Ψ ^ 2 * (sN * β ^ 4) := mul_le_mul_of_nonneg_left h.small hc
    _ = _ := by ring

/-- `u ℓ ≤ c₁ e² β⁴`. -/
private lemma AwSc.uell (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) : e * Ψ * ℓ ≤ c₁ * e ^ 2 * β ^ 4 := by
  refine aw_le_of_sq (by have := h.c1; have := h.e1; positivity) ?_
  have e1 : (e * Ψ * ℓ) ^ 2 = c₁ * e ^ 3 * (Nr * Ψ ^ 4) := by
    rw [mul_pow, h.ell2]; ring
  rw [e1]
  have h4 := h.NPsi4
  have hc : 0 ≤ c₁ * e ^ 3 := by have := h.c1; have := h.e1; positivity
  calc c₁ * e ^ 3 * (Nr * Ψ ^ 4) ≤ c₁ * e ^ 3 * β ^ 8 := mul_le_mul_of_nonneg_left h4 hc
    _ ≤ c₁ ^ 2 * e ^ 4 * β ^ 8 := by
        have : c₁ * e ^ 3 ≤ c₁ ^ 2 * e ^ 4 := by
          have := h.c1; have := h.e1
          have : c₁ ≤ c₁ ^ 2 := by nlinarith
          have : e ^ 3 ≤ e ^ 4 := pow_le_pow_right₀ h.e1 (by norm_num)
          have : 0 ≤ e ^ 3 := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = (c₁ * e ^ 2 * β ^ 4) ^ 2 := by ring

/-- `u² ℓ ≤ c₁ e³ Ψ β⁴`. -/
private lemma AwSc.u2ell (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) :
    (e * Ψ) ^ 2 * ℓ ≤ c₁ * e ^ 3 * Ψ * β ^ 4 := by
  have h1 := h.uell
  have h2 := h.u1
  have hΨ := h.psi
  have he := h.e1
  calc (e * Ψ) ^ 2 * ℓ = (e * Ψ) * (e * Ψ * ℓ) := by ring
    _ ≤ (e * Ψ) * (c₁ * e ^ 2 * β ^ 4) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c₁ * e ^ 3 * Ψ * β ^ 4 := by ring

/-- `e ℓ ≤ c₁ e² √N β²`. -/
private lemma AwSc.eell (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) : e * ℓ ≤ c₁ * e ^ 2 * sN * β ^ 2 := by
  have hs := h.sN0
  refine aw_le_of_sq (by have := h.c1; have := h.e1; have := h.β0; positivity) ?_
  have e1 : (e * ℓ) ^ 2 = c₁ * e ^ 3 * (Nr * Ψ ^ 2) := by rw [mul_pow, h.ell2]; ring
  rw [e1]
  have hc : 0 ≤ c₁ * e ^ 3 := by have := h.c1; have := h.e1; positivity
  calc _ ≤ c₁ * e ^ 3 * (sN * β ^ 4) := mul_le_mul_of_nonneg_left h.small hc
    _ ≤ c₁ ^ 2 * e ^ 4 * (sN * sN) * β ^ 4 := by
        have : c₁ * e ^ 3 * sN ≤ c₁ ^ 2 * e ^ 4 * (sN * sN) := by
          have := h.c1; have := h.e1
          have : c₁ ≤ c₁ ^ 2 := by nlinarith
          have : e ^ 3 ≤ e ^ 4 := pow_le_pow_right₀ h.e1 (by norm_num)
          have : sN ≤ sN * sN := by nlinarith
          have : 0 ≤ e ^ 3 := by positivity
          have : c₁ * e ^ 3 ≤ c₁ ^ 2 * e ^ 4 := by nlinarith
          nlinarith
        have := h.β0
        nlinarith [pow_pos h.β0 4]
    _ = (c₁ * e ^ 2 * sN * β ^ 2) ^ 2 := by ring


/-- The order-three, one-factor bound: `(2/N) Q₁ + 64 B² ℓ² ≤ 88 c₁² (T+1)² N √N D Ψ²`. -/
private lemma AwSc.sc1 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) :
    2 / Nr * (Nr * ℓ ^ 4 + (Nr * (T + e * Ψ) * ((2 * ℓ * T * sN) * ℓ) +
      Nr * (e * Ψ) * ((2 * ℓ * T * sN) * ℓ) + (e * Ψ) ^ 2 * (Nr * (sN * ℓ) / η)) +
      2 * (Nr * (ℓ ^ 2 * (2 * (T + e * Ψ) * T * sN)) + e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ)))) +
      Nr * (4 * (4 * (T + e * Ψ)) ^ 2 * ℓ ^ 2 / Nr) ≤
      88 * c₁ ^ 2 * (T + 1) ^ 2 * (Nr * sN * (D * Ψ ^ 2)) := by
  have hN := h.N1
  have hN0 : Nr ≠ 0 := by linarith
  have hs := h.sN0
  have hΨ := h.psi
  have he := h.e1
  have hT := h.T1
  have hc := h.c1
  have hu := h.u1
  have hβ := h.β0
  have hβ1 := h.β1
  have hℓ := h.ell
  have hη := h.eta
  have hD1 : e ≤ D := by have := h.eD1 (k := 1) (by norm_num); rwa [pow_one] at this
  have hu0 : 0 ≤ e * Ψ := by positivity
  set Z := Nr * sN * (D * Ψ ^ 2) with hZ
  have hZ0 : 0 ≤ Z := by have := h.D0; positivity
  have hℓ2 := h.ell2
  -- ℓ² ≤ c₁ D N Ψ²
  have hl2 : ℓ ^ 2 * sN ≤ c₁ * Z := by
    rw [hℓ2, hZ]
    have : c₁ * e * Nr * Ψ ^ 2 * sN ≤ c₁ * D * Nr * Ψ ^ 2 * sN := by gcongr
    linarith
  have t1 : 2 / Nr * (Nr * ℓ ^ 4) ≤ 2 * c₁ ^ 2 * Z := by
    have e1 : 2 / Nr * (Nr * ℓ ^ 4) = 2 * ℓ ^ 4 := by field_simp
    rw [e1]
    have := h.ell4
    have h2 : c₁ ^ 2 * e ^ 2 * (Nr * sN) * Ψ ^ 2 * β ^ 4 ≤ c₁ ^ 2 * Z := by
      rw [hZ]
      have : e ^ 2 * β ^ 4 ≤ D := h.eDb (by norm_num)
      have h3 : 0 ≤ c₁ ^ 2 * (Nr * sN) * Ψ ^ 2 := by positivity
      nlinarith
    linarith
  have t2 : 2 / Nr * (Nr * (T + e * Ψ) * ((2 * ℓ * T * sN) * ℓ)) ≤ 4 * (T + 1) * T * c₁ * Z := by
    have e1 : 2 / Nr * (Nr * (T + e * Ψ) * ((2 * ℓ * T * sN) * ℓ)) =
        4 * (T + e * Ψ) * T * (ℓ ^ 2 * sN) := by field_simp; ring
    rw [e1]
    calc 4 * (T + e * Ψ) * T * (ℓ ^ 2 * sN) ≤ 4 * (T + 1) * T * (c₁ * Z) := by gcongr
      _ = _ := by ring
  have t3 : 2 / Nr * (Nr * (e * Ψ) * ((2 * ℓ * T * sN) * ℓ)) ≤ 4 * T * c₁ * Z := by
    have e1 : 2 / Nr * (Nr * (e * Ψ) * ((2 * ℓ * T * sN) * ℓ)) =
        4 * (e * Ψ) * T * (ℓ ^ 2 * sN) := by field_simp; ring
    rw [e1]
    calc 4 * (e * Ψ) * T * (ℓ ^ 2 * sN) ≤ 4 * 1 * T * (c₁ * Z) := by gcongr
      _ = _ := by ring
  have t4 : 2 / Nr * ((e * Ψ) ^ 2 * (Nr * (sN * ℓ) / η)) ≤ 2 * c₁ * Z := by
    have e1 : 2 / Nr * ((e * Ψ) ^ 2 * (Nr * (sN * ℓ) / η)) =
        2 * sN * ((e * Ψ) ^ 2 * ℓ) * η⁻¹ := by field_simp
    rw [e1]
    have h1 := h.u2ell
    have h2 := h.inv_eta
    calc 2 * sN * ((e * Ψ) ^ 2 * ℓ) * η⁻¹ ≤ 2 * sN * (c₁ * e ^ 3 * Ψ * β ^ 4) * (Nr * Ψ) := by
          gcongr
      _ = 2 * c₁ * (e ^ 3 * β ^ 4) * (Nr * sN * Ψ ^ 2) := by ring
      _ ≤ 2 * c₁ * D * (Nr * sN * Ψ ^ 2) := by
          have : e ^ 3 * β ^ 4 ≤ D := h.eDb (by norm_num)
          gcongr
      _ = 2 * c₁ * Z := by rw [hZ]; ring
  have t5 : 2 / Nr * (2 * (Nr * (ℓ ^ 2 * (2 * (T + e * Ψ) * T * sN)))) ≤
      8 * c₁ * (T + 1) * T * Z := by
    have e1 : 2 / Nr * (2 * (Nr * (ℓ ^ 2 * (2 * (T + e * Ψ) * T * sN)))) =
        8 * (T + e * Ψ) * T * (ℓ ^ 2 * sN) := by field_simp; ring
    rw [e1]
    calc 8 * (T + e * Ψ) * T * (ℓ ^ 2 * sN) ≤ 8 * (T + 1) * T * (c₁ * Z) := by gcongr
      _ = _ := by ring
  have t6 : 2 / Nr * (2 * (e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ)))) ≤ 4 * c₁ ^ 2 * Z := by
    have e1 : 2 / Nr * (2 * (e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ)))) =
        4 * (e * Ψ * ℓ) * (ℓ ^ 2 * sN) := by field_simp; ring
    rw [e1]
    have h1 := h.uell
    have h3 : e ^ 3 * β ^ 4 ≤ D := h.eDb (by norm_num)
    calc 4 * (e * Ψ * ℓ) * (ℓ ^ 2 * sN) ≤ 4 * (c₁ * e ^ 2 * β ^ 4) * (ℓ ^ 2 * sN) := by gcongr
      _ = 4 * c₁ ^ 2 * (e ^ 3 * β ^ 4) * (Nr * sN * Ψ ^ 2) := by rw [hℓ2]; ring
      _ ≤ 4 * c₁ ^ 2 * D * (Nr * sN * Ψ ^ 2) := by gcongr
      _ = 4 * c₁ ^ 2 * Z := by rw [hZ]; ring
  have t7 : Nr * (4 * (4 * (T + e * Ψ)) ^ 2 * ℓ ^ 2 / Nr) ≤ 64 * (T + 1) ^ 2 * c₁ * Z := by
    have e1 : Nr * (4 * (4 * (T + e * Ψ)) ^ 2 * ℓ ^ 2 / Nr) = 64 * (T + e * Ψ) ^ 2 * ℓ ^ 2 := by
      field_simp; ring
    rw [e1]
    have : ℓ ^ 2 ≤ ℓ ^ 2 * sN := le_mul_of_one_le_right (sq_nonneg _) hs
    calc 64 * (T + e * Ψ) ^ 2 * ℓ ^ 2 ≤ 64 * (T + 1) ^ 2 * (c₁ * Z) := by
          gcongr; linarith
      _ = _ := by ring
  have hcT : c₁ ≤ c₁ ^ 2 := by nlinarith
  have hc0 : 0 ≤ c₁ := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTa : (T + 1) * T ≤ (T + 1) ^ 2 := by nlinarith
  have hTb : T ≤ (T + 1) ^ 2 := by nlinarith
  have hTc : 1 ≤ (T + 1) ^ 2 := by nlinarith
  have hM : ∀ x y : ℝ, 0 ≤ x → x ≤ (T + 1) ^ 2 → 0 ≤ y → y ≤ c₁ ^ 2 →
      x * y * Z ≤ (c₁ ^ 2 * (T + 1) ^ 2) * Z := fun x y hx hx' hy hy' => by
    refine mul_le_mul_of_nonneg_right ?_ hZ0
    calc x * y ≤ (T + 1) ^ 2 * c₁ ^ 2 := mul_le_mul hx' hy' hy (by positivity)
      _ = c₁ ^ 2 * (T + 1) ^ 2 := by ring
  have k1 := hM 1 (c₁ ^ 2) zero_le_one hTc (by positivity) le_rfl
  have k2 := hM ((T + 1) * T) c₁ (by positivity) hTa hc0 hcT
  have k3 := hM T c₁ hT0 hTb hc0 hcT
  have k4 := hM 1 c₁ zero_le_one hTc hc0 hcT
  have k7 := hM ((T + 1) ^ 2) c₁ (by positivity) le_rfl hc0 hcT
  have hsum : 2 / Nr * (Nr * ℓ ^ 4 + (Nr * (T + e * Ψ) * ((2 * ℓ * T * sN) * ℓ) +
      Nr * (e * Ψ) * ((2 * ℓ * T * sN) * ℓ) + (e * Ψ) ^ 2 * (Nr * (sN * ℓ) / η)) +
      2 * (Nr * (ℓ ^ 2 * (2 * (T + e * Ψ) * T * sN)) + e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ)))) =
      2 / Nr * (Nr * ℓ ^ 4) + 2 / Nr * (Nr * (T + e * Ψ) * ((2 * ℓ * T * sN) * ℓ)) +
      2 / Nr * (Nr * (e * Ψ) * ((2 * ℓ * T * sN) * ℓ)) +
      2 / Nr * ((e * Ψ) ^ 2 * (Nr * (sN * ℓ) / η)) +
      2 / Nr * (2 * (Nr * (ℓ ^ 2 * (2 * (T + e * Ψ) * T * sN)))) +
      2 / Nr * (2 * (e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ)))) := by ring
  rw [hsum]
  linarith


/-- The order-three, two-factor bound. -/
private lemma AwSc.sc2 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) :
    2 / Nr ^ 2 * (2 * (ℓ ^ 2 * (2 * Nr * ℓ * T / η) + e * Ψ * (Nr * ℓ ^ 2 / η ^ 2)) +
      2 * (Nr * (ℓ ^ 2 * ((2 * ℓ * T * sN) * ℓ)) + e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ) / η))) +
      Nr * (4 * ℓ ^ 2 / Nr * (4 * (4 * (T + e * Ψ)) * ℓ ^ 2 / Nr)) ≤
      88 * c₁ ^ 2 * (T + 1) ^ 2 * (Nr * sN * ((D * Ψ ^ 2) ^ 2 + D * Ψ ^ 2 * (β / (Nr * η)))) := by
  have hN := h.N1
  have hN0 : Nr ≠ 0 := by linarith
  have hs := h.sN0
  have hΨ := h.psi
  have he := h.e1
  have hT := h.T1
  have hc := h.c1
  have hu := h.u1
  have hβ := h.β0
  have hβ1 := h.β1
  have hℓ := h.ell
  have hη := h.eta
  have hℓ2 := h.ell2
  have hD0 := h.D0
  set Z2 := Nr * sN * (D * Ψ ^ 2) ^ 2 with hZ2
  set Zb := sN * D * Ψ ^ 2 * β * η⁻¹ with hZb
  have hZ2' : 0 ≤ Z2 := by positivity
  have hZb' : 0 ≤ Zb := by positivity
  have hZbe : Nr * sN * (D * Ψ ^ 2 * (β / (Nr * η))) = Zb := by
    rw [hZb]; field_simp
  have hββ : β ^ 2 ≤ β := by nlinarith
  have hβ4 : β ^ 4 ≤ β := by nlinarith [pow_le_one₀ hβ.le hβ1 (n := 3), pow_pos hβ 3]
  have he2 : e ^ 2 ≤ D := h.eD1 (by norm_num)
  have he3 : e ^ 3 ≤ D := h.eD1 (by norm_num)
  have s1 : 2 / Nr ^ 2 * (2 * (ℓ ^ 2 * (2 * Nr * ℓ * T / η))) ≤ 8 * T * c₁ ^ 2 * Zb := by
    have e1 : 2 / Nr ^ 2 * (2 * (ℓ ^ 2 * (2 * Nr * ℓ * T / η))) =
        8 * T * c₁ * (e * ℓ) * Ψ ^ 2 * η⁻¹ := by
      rw [show ℓ ^ 2 * (2 * Nr * ℓ * T / η) = 2 * T * ℓ * (ℓ ^ 2) * Nr / η by ring, hℓ2]
      field_simp; ring
    rw [e1]
    have h1 := h.eell
    calc 8 * T * c₁ * (e * ℓ) * Ψ ^ 2 * η⁻¹
        ≤ 8 * T * c₁ * (c₁ * e ^ 2 * sN * β ^ 2) * Ψ ^ 2 * η⁻¹ := by
          gcongr
      _ = 8 * T * c₁ ^ 2 * (e ^ 2 * β ^ 2) * (sN * Ψ ^ 2 * η⁻¹) := by ring
      _ ≤ 8 * T * c₁ ^ 2 * (D * β) * (sN * Ψ ^ 2 * η⁻¹) := by
          gcongr
      _ = 8 * T * c₁ ^ 2 * Zb := by rw [hZb]; ring
  have s2 : 2 / Nr ^ 2 * (2 * (e * Ψ * (Nr * ℓ ^ 2 / η ^ 2))) ≤ 4 * c₁ * Zb := by
    have e1 : 2 / Nr ^ 2 * (2 * (e * Ψ * (Nr * ℓ ^ 2 / η ^ 2))) =
        4 * c₁ * e ^ 2 * Ψ ^ 3 * η⁻¹ * η⁻¹ := by
      rw [hℓ2]; field_simp; ring
    rw [e1]
    have h2 := h.inv_eta
    have hsm := h.small
    calc 4 * c₁ * e ^ 2 * Ψ ^ 3 * η⁻¹ * η⁻¹ ≤ 4 * c₁ * e ^ 2 * Ψ ^ 3 * η⁻¹ * (Nr * Ψ) := by gcongr
      _ = 4 * c₁ * e ^ 2 * (Nr * Ψ ^ 2) * (Ψ ^ 2 * η⁻¹) := by ring
      _ ≤ 4 * c₁ * e ^ 2 * (sN * β ^ 4) * (Ψ ^ 2 * η⁻¹) := by gcongr
      _ = 4 * c₁ * (e ^ 2 * β ^ 4) * (sN * Ψ ^ 2 * η⁻¹) := by ring
      _ ≤ 4 * c₁ * (D * β) * (sN * Ψ ^ 2 * η⁻¹) := by
          gcongr
      _ = 4 * c₁ * Zb := by rw [hZb]; ring
  have s3 : 2 / Nr ^ 2 * (2 * (Nr * (ℓ ^ 2 * ((2 * ℓ * T * sN) * ℓ)))) ≤ 8 * T * c₁ ^ 2 * Z2 := by
    have e1 : 2 / Nr ^ 2 * (2 * (Nr * (ℓ ^ 2 * ((2 * ℓ * T * sN) * ℓ)))) =
        8 * T * c₁ ^ 2 * e ^ 2 * (Nr * sN * Ψ ^ 4) := by
      rw [show ℓ ^ 2 * ((2 * ℓ * T * sN) * ℓ) = 2 * T * sN * (ℓ ^ 2) ^ 2 by ring, hℓ2]
      field_simp; ring
    rw [e1, hZ2]
    have : e ^ 2 ≤ D ^ 2 := le_trans he2 (by nlinarith)
    calc 8 * T * c₁ ^ 2 * e ^ 2 * (Nr * sN * Ψ ^ 4)
        ≤ 8 * T * c₁ ^ 2 * D ^ 2 * (Nr * sN * Ψ ^ 4) := by
          gcongr
      _ = _ := by ring
  have s4 : 2 / Nr ^ 2 * (2 * (e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ) / η))) ≤ 4 * c₁ ^ 2 * Zb := by
    have e1 : 2 / Nr ^ 2 * (2 * (e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ) / η))) =
        4 * sN * (e * Ψ * ℓ) * c₁ * e * Ψ ^ 2 * η⁻¹ := by
      rw [show e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ) / η) = e * Ψ * ℓ * (ℓ ^ 2) * Nr * sN / η by ring,
        hℓ2]
      field_simp; ring
    rw [e1]
    have h1 := h.uell
    calc 4 * sN * (e * Ψ * ℓ) * c₁ * e * Ψ ^ 2 * η⁻¹ ≤
          4 * sN * (c₁ * e ^ 2 * β ^ 4) * c₁ * e * Ψ ^ 2 * η⁻¹ := by gcongr
      _ = 4 * c₁ ^ 2 * (e ^ 3 * β ^ 4) * (sN * Ψ ^ 2 * η⁻¹) := by ring
      _ ≤ 4 * c₁ ^ 2 * (D * β) * (sN * Ψ ^ 2 * η⁻¹) := by
          gcongr
      _ = 4 * c₁ ^ 2 * Zb := by rw [hZb]; ring
  have d : Nr * (4 * ℓ ^ 2 / Nr * (4 * (4 * (T + e * Ψ)) * ℓ ^ 2 / Nr)) ≤
      64 * (T + 1) * c₁ ^ 2 * Z2 := by
    have e1 : Nr * (4 * ℓ ^ 2 / Nr * (4 * (4 * (T + e * Ψ)) * ℓ ^ 2 / Nr)) =
        64 * (T + e * Ψ) * c₁ ^ 2 * e ^ 2 * (Nr * Ψ ^ 4) := by
      rw [show 4 * ℓ ^ 2 / Nr * (4 * (4 * (T + e * Ψ)) * ℓ ^ 2 / Nr) =
        64 * (T + e * Ψ) * (ℓ ^ 2) ^ 2 / Nr ^ 2 by ring, hℓ2]
      field_simp
    rw [e1, hZ2]
    have : e ^ 2 ≤ D ^ 2 := le_trans he2 (by nlinarith)
    have hNs : Nr * Ψ ^ 4 ≤ Nr * sN * Ψ ^ 4 := by
      have : 0 ≤ Nr * Ψ ^ 4 := by positivity
      nlinarith
    calc 64 * (T + e * Ψ) * c₁ ^ 2 * e ^ 2 * (Nr * Ψ ^ 4) ≤
          64 * (T + 1) * c₁ ^ 2 * D ^ 2 * (Nr * sN * Ψ ^ 4) := by
          gcongr
      _ = _ := by ring
  have hc0 : 0 ≤ c₁ := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hcT : c₁ ≤ c₁ ^ 2 := le_self_pow₀ hc two_ne_zero
  have hTa : T + 1 ≤ (T + 1) ^ 2 := le_self_pow₀ (by linarith) two_ne_zero
  have hTb : T ≤ (T + 1) ^ 2 := by linarith
  have hTc : 1 ≤ (T + 1) ^ 2 := one_le_pow₀ (by linarith)
  have hM : ∀ x y W : ℝ, 0 ≤ W → 0 ≤ x → x ≤ (T + 1) ^ 2 → 0 ≤ y → y ≤ c₁ ^ 2 →
      x * y * W ≤ (c₁ ^ 2 * (T + 1) ^ 2) * W := fun x y W hW hx hx' hy hy' => by
    refine mul_le_mul_of_nonneg_right ?_ hW
    calc x * y ≤ (T + 1) ^ 2 * c₁ ^ 2 := mul_le_mul hx' hy' hy (by positivity)
      _ = c₁ ^ 2 * (T + 1) ^ 2 := by ring
  have k1 := hM T (c₁ ^ 2) Zb hZb' hT0 hTb (by positivity) le_rfl
  have k2 := hM 1 c₁ Zb hZb' zero_le_one hTc hc0 hcT
  have k3 := hM T (c₁ ^ 2) Z2 hZ2' hT0 hTb (by positivity) le_rfl
  have k4 := hM 1 (c₁ ^ 2) Zb hZb' zero_le_one hTc (by positivity) le_rfl
  have k5 := hM (T + 1) (c₁ ^ 2) Z2 hZ2' (by positivity) hTa (by positivity) le_rfl
  have hsum : 2 / Nr ^ 2 * (2 * (ℓ ^ 2 * (2 * Nr * ℓ * T / η) + e * Ψ * (Nr * ℓ ^ 2 / η ^ 2)) +
      2 * (Nr * (ℓ ^ 2 * ((2 * ℓ * T * sN) * ℓ)) + e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ) / η))) =
      2 / Nr ^ 2 * (2 * (ℓ ^ 2 * (2 * Nr * ℓ * T / η))) +
      2 / Nr ^ 2 * (2 * (e * Ψ * (Nr * ℓ ^ 2 / η ^ 2))) +
      2 / Nr ^ 2 * (2 * (Nr * (ℓ ^ 2 * ((2 * ℓ * T * sN) * ℓ)))) +
      2 / Nr ^ 2 * (2 * (e * Ψ * ℓ ^ 2 * (Nr * (sN * ℓ) / η))) := by ring
  have hR : 88 * c₁ ^ 2 * (T + 1) ^ 2 * (Nr * sN * ((D * Ψ ^ 2) ^ 2 + D * Ψ ^ 2 * (β / (Nr * η)))) =
      88 * (c₁ ^ 2 * (T + 1) ^ 2) * Z2 + 88 * (c₁ ^ 2 * (T + 1) ^ 2) * Zb := by
    rw [← hZbe, hZ2]; ring
  have hm1 : 0 ≤ c₁ ^ 2 * (T + 1) ^ 2 * Zb := by positivity
  have hm2 : 0 ≤ c₁ ^ 2 * (T + 1) ^ 2 * Z2 := by positivity
  rw [hsum, hR]
  linarith

/-- The order-three, three-factor bound. -/
private lemma AwSc.sc3 (h : AwSc Nr sN η Ψ e T c₁ D β ℓ) :
    8 / Nr ^ 3 * (ℓ ^ 2 * (Nr * ℓ ^ 2 / η ^ 2)) + Nr * (4 * ℓ ^ 2 / Nr) ^ 3 ≤
      72 * c₁ ^ 3 * (Nr * sN * ((D * Ψ ^ 2) ^ 3 + D * Ψ ^ 2 * (β / (Nr * η)) ^ 2)) := by
  have hN := h.N1
  have hN0 : Nr ≠ 0 := by linarith
  have hs := h.sN0
  have hΨ := h.psi
  have he := h.e1
  have hc := h.c1
  have hβ := h.β0
  have hβ1 := h.β1
  have hη := h.eta
  have hℓ2 := h.ell2
  have hD0 := h.D0
  have he3 : e ^ 3 ≤ D := h.eD1 (by norm_num)
  have r1 : 8 / Nr ^ 3 * (ℓ ^ 2 * (Nr * ℓ ^ 2 / η ^ 2)) ≤
      8 * c₁ ^ 2 * (Nr * sN * (D * Ψ ^ 2 * (β / (Nr * η)) ^ 2)) := by
    have e1 : 8 / Nr ^ 3 * (ℓ ^ 2 * (Nr * ℓ ^ 2 / η ^ 2)) = 8 * ℓ ^ 4 / (Nr ^ 2 * η ^ 2) := by
      field_simp
    have e2 : Nr * sN * (D * Ψ ^ 2 * (β / (Nr * η)) ^ 2) =
        (Nr * sN) * D * Ψ ^ 2 * β ^ 2 / (Nr ^ 2 * η ^ 2) := by field_simp
    rw [e1, e2]
    have h4 := h.ell4
    have hb : e ^ 2 * β ^ 4 ≤ D * β ^ 2 := by
      have : β ^ 4 ≤ β ^ 2 := pow_le_pow_of_le_one hβ.le hβ1 (by norm_num)
      exact mul_le_mul (h.eD1 (by norm_num)) this (by positivity) (by linarith)
    have : ℓ ^ 4 ≤ c₁ ^ 2 * (Nr * sN) * D * Ψ ^ 2 * β ^ 2 := by
      calc ℓ ^ 4 ≤ c₁ ^ 2 * e ^ 2 * (Nr * sN) * Ψ ^ 2 * β ^ 4 := h4
        _ = c₁ ^ 2 * (Nr * sN) * Ψ ^ 2 * (e ^ 2 * β ^ 4) := by ring
        _ ≤ c₁ ^ 2 * (Nr * sN) * Ψ ^ 2 * (D * β ^ 2) := by gcongr
        _ = _ := by ring
    calc 8 * ℓ ^ 4 / (Nr ^ 2 * η ^ 2) ≤ 8 * (c₁ ^ 2 * (Nr * sN) * D * Ψ ^ 2 * β ^ 2) /
          (Nr ^ 2 * η ^ 2) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have d : Nr * (4 * ℓ ^ 2 / Nr) ^ 3 ≤ 64 * c₁ ^ 3 * (Nr * sN * (D * Ψ ^ 2) ^ 3) := by
    have e1 : Nr * (4 * ℓ ^ 2 / Nr) ^ 3 = 64 * c₁ ^ 3 * e ^ 3 * (Nr * Ψ ^ 6) := by
      rw [div_pow, mul_pow, show (ℓ ^ 2) ^ 3 = (ℓ ^ 2) ^ 3 by rfl, hℓ2]
      field_simp; ring
    rw [e1]
    have : e ^ 3 ≤ D ^ 3 :=
      le_trans he3 (by nlinarith [pow_le_pow_right₀ hD0 (show 1 ≤ 3 by norm_num)])
    have hNs : Nr * Ψ ^ 6 ≤ Nr * sN * Ψ ^ 6 := by
      have : 0 ≤ Nr * Ψ ^ 6 := by positivity
      nlinarith
    calc 64 * c₁ ^ 3 * e ^ 3 * (Nr * Ψ ^ 6) ≤ 64 * c₁ ^ 3 * D ^ 3 * (Nr * sN * Ψ ^ 6) := by
          gcongr
      _ = _ := by ring
  have hc2 : c₁ ^ 2 ≤ c₁ ^ 3 := pow_le_pow_right₀ hc (by norm_num)
  have hW : 0 ≤ Nr * sN * (D * Ψ ^ 2 * (β / (Nr * η)) ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right hc2 hW
  have hR : 72 * c₁ ^ 3 * (Nr * sN * ((D * Ψ ^ 2) ^ 3 + D * Ψ ^ 2 * (β / (Nr * η)) ^ 2)) =
      72 * c₁ ^ 3 * (Nr * sN * (D * Ψ ^ 2) ^ 3) +
        72 * c₁ ^ 3 * (Nr * sN * (D * Ψ ^ 2 * (β / (Nr * η)) ^ 2)) := by ring
  have hz1 : 0 ≤ c₁ ^ 3 * (Nr * sN * (D * Ψ ^ 2) ^ 3) := by positivity
  have hz2 : 0 ≤ c₁ ^ 3 * (Nr * sN * (D * Ψ ^ 2 * (β / (Nr * η)) ^ 2)) := by positivity
  rw [hR]
  linarith

end ScFacts

end Scalar

/-! ## The order-three sum over the entries -/

section Order3

variable {N : ℕ}

/-- A sum over `{i ≤ j}` splits into the part `i < j` and the diagonal. -/
private lemma aw_upper_split {M : Type*} [AddCommMonoid M] (g : UpperIdx N → M) :
    ∑ α, g α = ∑ i, ∑ j, (if h : i < j then g ⟨(i, j), h.le⟩ else 0) + ∑ i, g ⟨(i, i), le_rfl⟩ := by
  set f : Fin N × Fin N → M := fun q => if h : q.1 ≤ q.2 then g ⟨q, h⟩ else 0 with hf
  have h1 : ∑ α, g α = ∑ q, f q := by
    have := Finset.sum_subtype (Finset.univ.filter fun q : Fin N × Fin N => q.1 ≤ q.2)
      (p := fun q : Fin N × Fin N => q.1 ≤ q.2) (F := (inferInstance : Fintype (UpperIdx N)))
      (by simp) f
    rw [Finset.sum_filter] at this
    have e : ∀ q : Fin N × Fin N, (if q.1 ≤ q.2 then f q else 0) = f q := fun q => by
      by_cases hq : q.1 ≤ q.2 <;> simp [hf, hq]
    simp_rw [e] at this
    rw [this]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp [hf, α.2]
  rw [h1, Fintype.sum_prod_type]
  have h2 : ∀ i j, f (i, j) = (if h : i < j then g ⟨(i, j), h.le⟩ else 0) +
      (if h : i = j then g ⟨(i, j), h.le⟩ else 0) := fun i j => by
    simp only [hf]
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij.le, hij, hij.ne]
    · subst hij; simp
    · simp [not_le.2 hij, not_lt.2 hij.le, hij.ne']
  simp_rw [h2, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_dite_eq]
  simp

private lemma awCj_mul (b : Bool) (σ y : ℂ) : σ * awCj b y = awCj b (awCj b σ * y) := by
  cases b <;> simp [awCj]

private lemma awCj_mul2 (b b' : Bool) (σ x y : ℂ) :
    σ * (awCj b x * awCj b' y) = awCj b' (awCj b' σ * (awCj (xor b b') x * y)) := by
  cases b <;> cases b' <;> simp [awCj]

private lemma awCj_sum (b : Bool) (f : Fin N → Fin N → ℂ) :
    ∑ i, ∑ j, awCj b (f i j) = awCj b (∑ i, ∑ j, f i j) := by
  cases b <;> simp [awCj, map_sum]

private lemma awCj_real (b : Bool) (c : ℝ) (x : ℂ) : awCj b ((c : ℂ) * x) = c * awCj b x := by
  cases b <;> simp [awCj]

/-- The coefficients `a_1, a_2, a_3` for an off-diagonal entry `i ≠ j`. -/
private lemma aw_coeff123 {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    (z : ℂ) {i j : Fin N} (hij : i ≠ j) :
    avgCoeffW A Wm z i j 1 = ((-2 / N : ℝ) : ℂ) * (GW A Wm z * GW A Wm z) i j ∧
      avgCoeffW A Wm z i j 2 = ((1 / N : ℝ) : ℂ) * awTr2 (GW A Wm z) i j ∧
      avgCoeffW A Wm z i j 3 = ((-2 / N : ℝ) : ℂ) * awTr3 (GW A Wm z) i j := by
  have hG := aw_GW_symm hA hW z
  refine ⟨?_, ?_, ?_⟩
  · unfold avgCoeffW
    rw [aw_tr1 hij hG]
    push_cast
    simp
    ring
  · unfold avgCoeffW
    rw [aw_tr2 hij hG]
    push_cast
    simp [awTr2]
  · unfold avgCoeffW
    rw [aw_tr3 hij hG]
    push_cast
    simp [awTr3]
    ring


/-- A sum over `{i ≤ j}`, bounded through its off-diagonal part and its diagonal terms. -/
private lemma aw_split_le (F : UpperIdx N → ℂ) (off : Fin N → Fin N → ℂ) (dg : ℝ)
    (hoff : ∀ i j, (if h : i < j then F ⟨(i, j), h.le⟩ else 0) = off i j)
    (hdg : ∀ i, ‖F ⟨(i, i), le_rfl⟩‖ ≤ dg) :
    ‖∑ α, F α‖ ≤ ‖∑ i, ∑ j, off i j‖ + N * dg := by
  rw [aw_upper_split F]
  simp_rw [hoff]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _i : Fin N, dg := Finset.sum_le_sum fun i _ => hdg i
    _ = _ := by simp

section C3

variable {A Wm : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {P : Matrix (Fin N) (Fin N) ℂ}
  {s : UpperIdx N → ℂ} {η Ψ e T c₁ D β ℓ : ℝ}

/-- The one-factor order-three sum `|∑_α s_α a_3^{(α)}|` (or with `ā_3`). -/
private lemma aw_c3_one (hA : A.IsHermitian) (hW : Wmᵀ = Wm) (hs : ∀ α, ‖s α‖ ≤ 1)
    (hsc : AwSc N (Real.sqrt N) η Ψ e T c₁ D β ℓ)
    (ev : ∀ b0 : Bool, AwEv N (GW A Wm z) P (fun i j => awCj b0 (awSig s i j)) η ℓ
      (2 * ℓ * T * Real.sqrt N) (2 * (T + e * Ψ) * T * Real.sqrt N) (e * Ψ) (T + e * Ψ) T)
    (b0 : Bool) :
    ‖∑ α : UpperIdx N, s α * awCj b0 (avgCoeffW A Wm z α.1.1 α.1.2 3)‖ ≤
      88 * c₁ ^ 2 * (T + 1) ^ 2 * (N * Real.sqrt N * (D * Ψ ^ 2)) := by
  have hN0 : (N : ℝ) ≠ 0 := by have := hsc.N1; linarith
  have hoff : ∀ i j, (if h : i < j then s ⟨(i, j), h.le⟩ *
      awCj b0 (avgCoeffW A Wm z i j 3) else 0) =
      awCj b0 (((-2 / N : ℝ) : ℂ) * (awCj b0 (awSig s i j) * awTr3 (GW A Wm z) i j)) := by
    intro i j
    by_cases h : i < j
    · simp only [h, ↓reduceDIte, awSig]
      rw [(aw_coeff123 hA hW z h.ne).2.2, awCj_mul]
      congr 1; ring
    · simp only [h, ↓reduceDIte, awSig]
      cases b0 <;> simp [awCj]
  have hdg : ∀ i, ‖s ⟨(i, i), le_rfl⟩ * awCj b0 (avgCoeffW A Wm z i i 3)‖ ≤
      4 * (4 * (T + e * Ψ)) ^ 2 * ℓ ^ 2 / N := fun i => by
    rw [norm_mul, awCj_norm]
    calc ‖s ⟨(i, i), le_rfl⟩‖ * ‖avgCoeffW A Wm z i i 3‖ ≤ 1 * ‖avgCoeffW A Wm z i i 3‖ :=
          mul_le_mul_of_nonneg_right (hs _) (norm_nonneg _)
      _ ≤ _ := by
          rw [one_mul]
          exact aw_avgCoeff_le (ev false).B0 (ev false).bdd (ev false).H_le i i 2
  refine (aw_split_le _ _ _ hoff hdg).trans ?_
  rw [awCj_sum, awCj_norm]
  have e1 : ∑ i, ∑ j, ((-2 / N : ℝ) : ℂ) * (awCj b0 (awSig s i j) * awTr3 (GW A Wm z) i j) =
      ((-2 / N : ℝ) : ℂ) * ∑ i, ∑ j, awCj b0 (awSig s i j) * awTr3 (GW A Wm z) i j := by
    simp_rw [Finset.mul_sum]
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show |(-2 / (N : ℝ))| = 2 / N by rw [abs_div, abs_neg]; simp]
  have hQ := (ev b0).Q1
  have h2N : 0 ≤ 2 / (N : ℝ) := by positivity
  refine le_trans ?_ hsc.sc1
  gcongr

/-- The two-factor order-three sum `|∑_α s_α a_1^{(α)} a_2^{(α)}|` (with conjugations). -/
private lemma aw_c3_two (hA : A.IsHermitian) (hW : Wmᵀ = Wm) (hs : ∀ α, ‖s α‖ ≤ 1)
    (hsc : AwSc N (Real.sqrt N) η Ψ e T c₁ D β ℓ)
    (ev : ∀ b0 : Bool, AwEv N (GW A Wm z) P (fun i j => awCj b0 (awSig s i j)) η ℓ
      (2 * ℓ * T * Real.sqrt N) (2 * (T + e * Ψ) * T * Real.sqrt N) (e * Ψ) (T + e * Ψ) T)
    (b0 b1 : Bool) :
    ‖∑ α : UpperIdx N, s α * (awCj b0 (avgCoeffW A Wm z α.1.1 α.1.2 1) *
      awCj b1 (avgCoeffW A Wm z α.1.1 α.1.2 2))‖ ≤
      88 * c₁ ^ 2 * (T + 1) ^ 2 *
        (N * Real.sqrt N * ((D * Ψ ^ 2) ^ 2 + D * Ψ ^ 2 * (β / (N * η)))) := by
  have hN0 : (N : ℝ) ≠ 0 := by have := hsc.N1; linarith
  have hoff : ∀ i j, (if h : i < j then s ⟨(i, j), h.le⟩ *
      (awCj b0 (avgCoeffW A Wm z i j 1) * awCj b1 (avgCoeffW A Wm z i j 2)) else 0) =
      awCj b1 ((((-2 / N) * (1 / N) : ℝ) : ℂ) * (awCj b1 (awSig s i j) *
        (awCj (xor b0 b1) ((GW A Wm z * GW A Wm z) i j) * awTr2 (GW A Wm z) i j))) := by
    intro i j
    by_cases h : i < j
    · simp only [h, ↓reduceDIte, awSig]
      obtain ⟨e1, e2, -⟩ := aw_coeff123 hA hW z h.ne
      rw [e1, e2, awCj_mul2, awCj_real]
      congr 1; push_cast; ring
    · simp only [h, ↓reduceDIte, awSig]
      cases b0 <;> cases b1 <;> simp [awCj]
  have hdg : ∀ i, ‖s ⟨(i, i), le_rfl⟩ * (awCj b0 (avgCoeffW A Wm z i i 1) *
      awCj b1 (avgCoeffW A Wm z i i 2))‖ ≤
      4 * ℓ ^ 2 / N * (4 * (4 * (T + e * Ψ)) * ℓ ^ 2 / N) := fun i => by
    rw [norm_mul, norm_mul, awCj_norm, awCj_norm]
    have h0 := aw_avgCoeff_le (ev false).B0 (ev false).bdd (ev false).H_le i i 0
    have h1' := aw_avgCoeff_le (ev false).B0 (ev false).bdd (ev false).H_le i i 1
    simp only [pow_zero, mul_one, pow_one, zero_add] at h0 h1'
    calc ‖s ⟨(i, i), le_rfl⟩‖ * (‖avgCoeffW A Wm z i i 1‖ * ‖avgCoeffW A Wm z i i 2‖)
        ≤ 1 * (‖avgCoeffW A Wm z i i 1‖ * ‖avgCoeffW A Wm z i i 2‖) :=
          mul_le_mul_of_nonneg_right (hs _) (by positivity)
      _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul h0 h1' (norm_nonneg _) (by have := hsc.ell; positivity)
  refine (aw_split_le _ _ _ hoff hdg).trans ?_
  rw [awCj_sum, awCj_norm]
  have e1 : ∑ i, ∑ j, (((-2 / N) * (1 / N) : ℝ) : ℂ) * (awCj b1 (awSig s i j) *
      (awCj (xor b0 b1) ((GW A Wm z * GW A Wm z) i j) * awTr2 (GW A Wm z) i j)) =
      (((-2 / N) * (1 / N) : ℝ) : ℂ) * ∑ i, ∑ j, awCj b1 (awSig s i j) *
        (awCj (xor b0 b1) ((GW A Wm z * GW A Wm z) i j) * awTr2 (GW A Wm z) i j) := by
    simp_rw [Finset.mul_sum]
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show |(-2 / (N : ℝ)) * (1 / N)| = 2 / (N : ℝ) ^ 2 by
      rw [abs_mul, abs_div, abs_neg, abs_div]; simp; field_simp]
  have hQ := (ev b1).Q2 (xor b0 b1)
  have h2N : 0 ≤ 2 / (N : ℝ) ^ 2 := by positivity
  refine le_trans ?_ hsc.sc2
  gcongr

/-- The three-factor order-three sum `∑_α |a_1^{(α)}|³`. -/
private lemma aw_c3_three (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    (hsc : AwSc N (Real.sqrt N) η Ψ e T c₁ D β ℓ)
    (ev : AwEv N (GW A Wm z) P (fun i j => awCj false (awSig s i j)) η ℓ
      (2 * ℓ * T * Real.sqrt N) (2 * (T + e * Ψ) * T * Real.sqrt N) (e * Ψ) (T + e * Ψ) T) :
    ∑ α : UpperIdx N, ‖avgCoeffW A Wm z α.1.1 α.1.2 1‖ ^ 3 ≤
      72 * c₁ ^ 3 * (N * Real.sqrt N * ((D * Ψ ^ 2) ^ 3 + D * Ψ ^ 2 * (β / (N * η)) ^ 2)) := by
  rw [aw_upper_split (fun α : UpperIdx N => ‖avgCoeffW A Wm z α.1.1 α.1.2 1‖ ^ 3)]
  have hoff : ∀ i j, (if h : i < j then ‖avgCoeffW A Wm z i j 1‖ ^ 3 else 0) ≤
      (2 / N) ^ 3 * ‖(GW A Wm z * GW A Wm z) i j‖ ^ 3 := fun i j => by
    by_cases h : i < j
    · simp only [h, ↓reduceDIte]
      rw [(aw_coeff123 hA hW z h.ne).1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        show |(-2 / (N : ℝ))| = 2 / N by rw [abs_div, abs_neg]; simp, mul_pow]
    · simp only [h, ↓reduceDIte]; positivity
  have hdg : ∀ i, ‖avgCoeffW A Wm z i i 1‖ ^ 3 ≤ (4 * ℓ ^ 2 / N) ^ 3 := fun i => by
    have h0 := aw_avgCoeff_le ev.B0 ev.bdd ev.H_le i i 0
    simp only [pow_zero, mul_one, zero_add] at h0
    exact pow_le_pow_left₀ (norm_nonneg _) h0 3
  have hQ := ev.sumH3
  have hA1 : ∑ i, ∑ j, (if h : i < j then ‖avgCoeffW A Wm z i j 1‖ ^ 3 else 0) ≤
      8 / (N : ℝ) ^ 3 * (ℓ ^ 2 * (N * ℓ ^ 2 / η ^ 2)) := by
    calc _ ≤ ∑ i, ∑ j, (2 / N) ^ 3 * ‖(GW A Wm z * GW A Wm z) i j‖ ^ 3 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hoff i j
      _ = (2 / (N : ℝ)) ^ 3 * ∑ i, ∑ j, ‖(GW A Wm z * GW A Wm z) i j‖ ^ 3 := by
          simp_rw [Finset.mul_sum]
      _ ≤ (2 / (N : ℝ)) ^ 3 * (ℓ ^ 2 * (N * ℓ ^ 2 / η ^ 2)) := by gcongr
      _ = _ := by ring
  have hA2 : ∑ i : Fin N, ‖avgCoeffW A Wm z i i 1‖ ^ 3 ≤ N * (4 * ℓ ^ 2 / N) ^ 3 := by
    calc _ ≤ ∑ _i : Fin N, (4 * ℓ ^ 2 / N) ^ 3 := Finset.sum_le_sum fun i _ => hdg i
      _ = _ := by simp
  exact (add_le_add hA1 hA2).trans hsc.sc3

end C3

/-- Assembly of the order-three bounds through the decomposition of `f_3`. -/
private lemma aw_c3_final (p : ℕ) {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1)
    (a : UpperIdx N → ℕ → ℂ) (a0 : ℂ) (h0 : ∀ α, a α 0 = a0) {L K₀ X b c₁ T : ℝ}
    (hL : 0 ≤ L) (hX0 : 0 ≤ X) (hb0 : 0 ≤ b)
    (hK88 : 88 * c₁ ^ 2 * (T + 1) ^ 2 ≤ K₀) (hK72 : 72 * c₁ ^ 3 ≤ K₀) (hK1 : 1 ≤ K₀)
    (h1 : ∀ b0 : Bool, ‖∑ α, s α * awCj b0 (a α 3)‖ ≤ 88 * c₁ ^ 2 * (T + 1) ^ 2 * (L * X))
    (h2 : ∀ b0 b1 : Bool, ‖∑ α, s α * (awCj b0 (a α 1) * awCj b1 (a α 2))‖ ≤
      88 * c₁ ^ 2 * (T + 1) ^ 2 * (L * (X ^ 2 + X * b)))
    (h3 : ∑ α, ‖a α 1‖ ^ 3 ≤ 72 * c₁ ^ 3 * (L * (X ^ 3 + X * b ^ 2))) :
    ‖∑ α, s α * fCoeff p (a α) 3‖ ≤ 4 ^ p * (L * (‖a0‖ ^ p + (K₀ * (X + b)) ^ p)) := by
  have hY : 0 ≤ K₀ * (X + b) := by positivity
  refine aw_fCoeff3 p s a a0 h0 hs hL hY (fun b0 => (h1 b0).trans ?_)
    (fun b0 b1 => (h2 b0 b1).trans ?_) (h3.trans ?_)
  · have h3' : L * X ≤ L * (X + b) := mul_le_mul_of_nonneg_left (by linarith) hL
    have h0' : 0 ≤ L * X := by positivity
    calc 88 * c₁ ^ 2 * (T + 1) ^ 2 * (L * X) ≤ K₀ * (L * (X + b)) :=
          mul_le_mul hK88 h3' h0' (by linarith)
      _ = _ := by ring
  · have h3' : X ^ 2 + X * b ≤ (X + b) ^ 2 := by
      have e := (show (X + b) ^ 2 = X ^ 2 + X * b + (X * b + b ^ 2) by ring)
      have := mul_nonneg hX0 hb0
      have := sq_nonneg b
      linarith
    have h4 : 88 * c₁ ^ 2 * (T + 1) ^ 2 ≤ K₀ ^ 2 := hK88.trans (le_self_pow₀ hK1 two_ne_zero)
    have h0' : 0 ≤ L * (X ^ 2 + X * b) := by positivity
    calc 88 * c₁ ^ 2 * (T + 1) ^ 2 * (L * (X ^ 2 + X * b)) ≤ K₀ ^ 2 * (L * (X + b) ^ 2) :=
          mul_le_mul h4 (mul_le_mul_of_nonneg_left h3' hL) h0' (by positivity)
      _ = _ := by ring
  · have h3' : X ^ 3 + X * b ^ 2 ≤ (X + b) ^ 3 := by
      have e := (show (X + b) ^ 3 = X ^ 3 + X * b ^ 2 + (3 * X ^ 2 * b + 2 * X * b ^ 2 + b ^ 3)
        by ring)
      have : 0 ≤ 3 * X ^ 2 * b + 2 * X * b ^ 2 + b ^ 3 := by positivity
      linarith
    have h4 : 72 * c₁ ^ 3 ≤ K₀ ^ 3 := hK72.trans (le_self_pow₀ hK1 (by norm_num))
    have h0' : 0 ≤ L * (X ^ 3 + X * b ^ 2) := by positivity
    calc 72 * c₁ ^ 3 * (L * (X ^ 3 + X * b ^ 2)) ≤ K₀ ^ 3 * (L * (X + b) ^ 3) :=
          mul_le_mul h4 (mul_le_mul_of_nonneg_left h3' hL) h0' (by positivity)
      _ = _ := by ring

/-- The constant `100 c₁³ (τ⁻¹ + 1)²` of the order-three bound. -/
private lemma aw_K0 {c₁ T : ℝ} (hc1 : 1 ≤ c₁) (hT : 0 ≤ T) :
    88 * c₁ ^ 2 * (T + 1) ^ 2 ≤ 100 * c₁ ^ 3 * (T + 1) ^ 2 ∧
      72 * c₁ ^ 3 ≤ 100 * c₁ ^ 3 * (T + 1) ^ 2 ∧ 1 ≤ 100 * c₁ ^ 3 * (T + 1) ^ 2 := by
  have h1 : 1 ≤ c₁ ^ 3 := one_le_pow₀ hc1
  have h2 : 1 ≤ (T + 1) ^ 2 := one_le_pow₀ (by linarith)
  have h12 : 1 ≤ c₁ ^ 3 * (T + 1) ^ 2 := one_le_mul_of_one_le_of_one_le h1 h2
  have h3 : c₁ ^ 2 ≤ c₁ ^ 3 := pow_le_pow_right₀ hc1 (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (T + 1))
  have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ c₁ ^ 3)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- `n = 3` on the event, case `u = N^{εa} Ψ ≤ 1`, under (b) at `z`. -/
private lemma aw_case3 {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {S : Set ℂ}
    (hS : StandingBoundW τ (specOf A) S) {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im) {κ e D β : ℝ}
    (hκ : 0 < κ) (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) (hD : e ^ 4 ≤ D)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hu : e * PsiW (specOf A) z ≤ 1)
    (hsmall : (N : ℝ) * PsiW (specOf A) z ^ 2 ≤ Real.sqrt N * β ^ 4)
    {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) (p : ℕ)
    (hE : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      e * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) * testNorm (awVec s (piW A z) l)) :
    ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) 3‖ ≤
      4 ^ p * ((N * Real.sqrt N) * (FtW A Wm z ^ p +
        (100 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ 3 * (τ⁻¹ + 1) ^ 2 *
          (D * PsiW (specOf A) z ^ 2 + β / (N * z.im))) ^ p)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hp1, -, -⟩ := aw_psi (a := specOf A) hN hz
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  have hc1 : 1 ≤ 2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1 := by
    have : 0 ≤ 2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) := by have := inv_pos.2 hκ; positivity
    linarith
  have hNη : 0 < (N : ℝ) * z.im := by positivity
  have hΨ0 : 0 ≤ PsiW (specOf A) z := le_trans (by positivity) hp1
  have hsc : AwSc N (Real.sqrt N) z.im (PsiW (specOf A) z) e τ⁻¹ (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1)
      D β (Real.sqrt ((2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) * e * N * PsiW (specOf A) z ^ 2)) :=
    { sN0 := Real.one_le_sqrt.2 hNr
      sN2 := Real.sq_sqrt (by linarith)
      eta := hz
      psi := hΨ0
      e1 := he
      T1 := hT1
      c1 := hc1
      eD := hD
      β0 := hβ0
      β1 := hβ1
      ell := Real.sqrt_nonneg _
      ell2 := Real.sq_sqrt (by positivity)
      u1 := hu
      etaPsi := by rw [div_le_iff₀ hNη] at hp1; linarith
      small := hsmall }
  have ev := fun b0 : Bool => aw_mkEv hN hA hW hτ hS hzS hz hκ hIm he hs hE b0
  obtain ⟨hK88, hK72, hK1⟩ := aw_K0 hc1 (by linarith : (0 : ℝ) ≤ τ⁻¹)
  exact aw_c3_final p hs (fun α : UpperIdx N => avgCoeffW A Wm z α.1.1 α.1.2)
    (mNW A Wm z - mW (specOf A) z) (fun α => aw_avgCoeff_zero A Wm z _ _)
    (by positivity) (by have := hsc.D0; positivity) (by positivity)
    hK88 hK72 hK1 (aw_c3_one hA hW hs hsc ev) (aw_c3_two hA hW hs hsc ev)
    (aw_c3_three hA hW hsc (ev false))

end Order3

/-! ## Entrywise bounds for the orders `n ≥ 4`, the deterministic bounds, and `F̃ ≤ u` -/

section Entry

variable {N : ℕ}

private lemma aw_card_upper : (Fintype.card (UpperIdx N) : ℝ) ≤ (N : ℝ) ^ 2 := by
  have := Fintype.card_subtype_le (fun q : Fin N × Fin N => q.1 ≤ q.2)
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  calc (Fintype.card (UpperIdx N) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast this
    _ = (N : ℝ) ^ 2 := by push_cast; ring

/-- `|∑_α s_α f_α| ≤ N² max |f_α|` for `|s_α| ≤ 1`. -/
private lemma aw_sum_entries {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) (f : UpperIdx N → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ α, ‖f α‖ ≤ M) : ‖∑ α, s α * f α‖ ≤ (N : ℝ) ^ 2 * M := by
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _α : UpperIdx N, M := Finset.sum_le_sum fun α _ => by
        rw [norm_mul]
        calc ‖s α‖ * ‖f α‖ ≤ 1 * M := mul_le_mul (hs α) (hf α) (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    _ = (Fintype.card (UpperIdx N) : ℝ) * M := by simp
    _ ≤ (N : ℝ) ^ 2 * M := mul_le_mul_of_nonneg_right aw_card_upper hM


/-- `|f_n| ≤ (n+1)^p (4B)^n (x^p + (ℓ²/N)^p)` when `|G| ≤ B` (`B ≥ 1`), `|G²| ≤ ℓ²`, `|a_0| ≤ x`. -/
private lemma aw_entry_fCoeff {A Wm : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {B ℓ x : ℝ} (hB : 1 ≤ B)
    (hG : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hH : ∀ a b, ‖(GW A Wm z * GW A Wm z) a b‖ ≤ ℓ ^ 2)
    (hx : 0 ≤ x) (i j : Fin N) (h0 : ‖avgCoeffW A Wm z i j 0‖ ≤ x) (p n : ℕ) :
    ‖fCoeff p (avgCoeffW A Wm z i j) n‖ ≤
      ((n : ℝ) + 1) ^ p * ((4 * B) ^ n * (x ^ p + (ℓ ^ 2 / N) ^ p)) := by
  have hB0 : 0 ≤ B := by linarith
  refine aw_fCoeff_le p n _ hx (by positivity) (by positivity) h0 fun k hk _ => ?_
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine (aw_avgCoeff_le hB0 hG hH i j k').trans ?_
  have h4 : (4 : ℝ) ≤ 4 * B := by linarith
  have hl : 0 ≤ ℓ ^ 2 / N := by positivity
  calc 4 * (4 * B) ^ k' * ℓ ^ 2 / N = 4 * (4 * B) ^ k' * (ℓ ^ 2 / N) := by ring
    _ ≤ (4 * B) * (4 * B) ^ k' * (ℓ ^ 2 / N) := by gcongr
    _ = (4 * B) ^ (k' + 1) * (ℓ ^ 2 / N) := by ring

/-- `F̃ ≤ u` when `|G − Π| ≤ u` entrywise (`N⁻¹ tr Π = m`). -/
private lemma aw_FtW_le_u {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : ∀ a b, ‖GW A Wm z a b - piW A z a b‖ ≤ u) :
    FtW A Wm z ≤ u := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold FtW mNW
  rw [← aw_trace_piW hN hA hz, ← mul_sub, ← Matrix.trace_sub, norm_mul, norm_inv,
    Complex.norm_natCast, Matrix.trace]
  calc (N : ℝ)⁻¹ * ‖∑ a, Matrix.diag (GW A Wm z - piW A z) a‖ ≤ (N : ℝ)⁻¹ * ∑ _a : Fin N, u :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by
          simpa using hu a a)) (inv_nonneg.2 hNr.le)
    _ = u := by simp; field_simp

/-- `N^{−n/2} N² = N^{2 − n/2}`. -/
private lemma aw_rpow_n2 {Nr : ℝ} (hN : 0 < Nr) (n : ℕ) :
    Nr ^ (-(n : ℝ) / 2) * Nr ^ 2 = Nr ^ ((2 : ℝ) - n / 2) := by
  rw [show (Nr ^ 2 : ℝ) = Nr ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hN]
  congr 1; push_cast; ring

/-- `N^a ≤ N^b` for `a ≤ b`, `N ≥ 1`, with `N^b` a natural power. -/
private lemma aw_rpow_le_pow {Nr : ℝ} (hN : 1 ≤ Nr) {a : ℝ} {k : ℕ} (h : a ≤ k) :
    Nr ^ a ≤ Nr ^ k := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hN h

/-- The exponent count for `εa > 1`: `N^{2−n/2} η^{−(n+p)} ≤ T^p (D (Nη)^{−2})^p` when `D ≥ N⁴`. -/
private lemma aw_exp_I {Nr η T D : ℝ} (hN : 1 ≤ Nr) (hη : 0 < η) (hηN : 1 ≤ Nr * η)
    (hηT : η ≤ T) (hT1 : 1 ≤ T) (hD : Nr ^ 4 ≤ D) {n p : ℕ} (hp : 2 ≤ p) (hn : n ≤ 4 * p) :
    Nr ^ ((2 : ℝ) - n / 2) * η⁻¹ ^ (n + p) ≤ T ^ p * (D * (1 / (Nr * η)) ^ 2) ^ p := by
  have hN0 : 0 < Nr := by linarith
  have hηi : η⁻¹ ≤ Nr := by rw [inv_le_iff_one_le_mul₀ hη]; linarith
  have hηi0 : 0 < η⁻¹ := inv_pos.2 hη
  have hTη : 1 ≤ T * η⁻¹ := by rw [← div_eq_mul_inv, one_le_div hη]; exact hηT
  have hTp : 1 ≤ T ^ p := one_le_pow₀ hT1
  -- the right side is at least `T^p N^{2p} η^{−2p}`
  have hR : T ^ p * (Nr ^ (2 * p) * η⁻¹ ^ (2 * p)) ≤ T ^ p * (D * (1 / (Nr * η)) ^ 2) ^ p := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e1 : (D * (1 / (Nr * η)) ^ 2) ^ p = D ^ p * ((Nr ^ (2 * p))⁻¹ * η⁻¹ ^ (2 * p)) := by
      rw [one_div, pow_mul, pow_mul]; ring
    rw [e1]
    have hD' : (Nr ^ 4) ^ p ≤ D ^ p := pow_le_pow_left₀ (by positivity) hD p
    rw [← pow_mul] at hD'
    have e2 : Nr ^ (2 * p) * η⁻¹ ^ (2 * p) =
        Nr ^ (4 * p) * ((Nr ^ (2 * p))⁻¹ * η⁻¹ ^ (2 * p)) := by
      rw [show 4 * p = 2 * p + 2 * p by ring, pow_add]; field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_right hD' (by positivity)
  refine le_trans ?_ hR
  rcases le_total p n with hpn | hpn
  · have e1 : η⁻¹ ^ (n + p) = η⁻¹ ^ (2 * p) * η⁻¹ ^ (n - p) := by
      rw [← pow_add]; congr 1; omega
    have h1 : η⁻¹ ^ (n - p) ≤ Nr ^ (n - p) := pow_le_pow_left₀ hηi0.le hηi _
    have h2 : Nr ^ ((2 : ℝ) - n / 2) * Nr ^ (n - p) ≤ Nr ^ (2 * p) := by
      rw [show (Nr ^ (n - p) : ℝ) = Nr ^ (((n - p : ℕ) : ℝ)) by rw [Real.rpow_natCast],
        ← Real.rpow_add hN0]
      refine aw_rpow_le_pow hN ?_
      have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      rw [Nat.cast_sub hpn]; push_cast; linarith
    rw [e1]
    calc Nr ^ ((2 : ℝ) - n / 2) * (η⁻¹ ^ (2 * p) * η⁻¹ ^ (n - p))
        ≤ Nr ^ ((2 : ℝ) - n / 2) * (η⁻¹ ^ (2 * p) * Nr ^ (n - p)) := by gcongr
      _ = (Nr ^ ((2 : ℝ) - n / 2) * Nr ^ (n - p)) * η⁻¹ ^ (2 * p) := by ring
      _ ≤ Nr ^ (2 * p) * η⁻¹ ^ (2 * p) := by gcongr
      _ ≤ T ^ p * (Nr ^ (2 * p) * η⁻¹ ^ (2 * p)) := le_mul_of_one_le_left (by positivity) hTp
  · have e1 : T ^ p * η⁻¹ ^ (2 * p) = η⁻¹ ^ (n + p) * ((T * η⁻¹) ^ (p - n) * T ^ n) := by
      rw [mul_pow, show T ^ p = T ^ (p - n) * T ^ n by rw [← pow_add]; congr 1; omega,
        show η⁻¹ ^ (2 * p) = η⁻¹ ^ (n + p) * η⁻¹ ^ (p - n) by rw [← pow_add]; congr 1; omega]
      ring
    have h1 : 1 ≤ (T * η⁻¹) ^ (p - n) * T ^ n :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hTη) (one_le_pow₀ hT1)
    have h2 : η⁻¹ ^ (n + p) ≤ T ^ p * η⁻¹ ^ (2 * p) := by
      rw [e1]; exact le_mul_of_one_le_right (by positivity) h1
    have h3 : Nr ^ ((2 : ℝ) - n / 2) ≤ Nr ^ (2 * p) := by
      refine aw_rpow_le_pow hN ?_
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      push_cast; linarith
    calc Nr ^ ((2 : ℝ) - n / 2) * η⁻¹ ^ (n + p) ≤ Nr ^ (2 * p) * (T ^ p * η⁻¹ ^ (2 * p)) :=
          mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = T ^ p * (Nr ^ (2 * p) * η⁻¹ ^ (2 * p)) := by ring

/-- The exponent count for `u = eΨ > 1`, `e ≤ N`, `n ≥ 4`:
`N^{2−n/2} u^{n+p} ≤ 2^n e^{2p} u^{2p}`. -/
private lemma aw_exp_II {Nr e u : ℝ} (hN : 1 ≤ Nr) (he : 1 ≤ e) (heN : e ≤ Nr) (hu1 : 1 ≤ u)
    (hu2 : u ≤ 2 * e) {n p : ℕ} (hp : 2 ≤ p) (hn4 : 4 ≤ n) (hn : n ≤ 4 * p) :
    Nr ^ ((2 : ℝ) - n / 2) * u ^ (n + p) ≤ 2 ^ n * e ^ (2 * p) * u ^ (2 * p) := by
  have hN0 : 0 < Nr := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hr1 : Nr ^ ((2 : ℝ) - n / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hN ?_
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hr0 : 0 ≤ Nr ^ ((2 : ℝ) - n / 2) := Real.rpow_nonneg hN0.le _
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have he2p : 1 ≤ e ^ (2 * p) := one_le_pow₀ he
  rcases le_total n p with hnp | hpn
  · have h1 : u ^ (n + p) ≤ u ^ (2 * p) := pow_le_pow_right₀ hu1 (by omega)
    calc Nr ^ ((2 : ℝ) - n / 2) * u ^ (n + p) ≤ 1 * u ^ (2 * p) :=
          mul_le_mul hr1 h1 (by positivity) zero_le_one
      _ ≤ 2 ^ n * e ^ (2 * p) * u ^ (2 * p) := by
          rw [one_mul]
          exact le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le h2n he2p)
  · have e1 : u ^ (n + p) = u ^ (2 * p) * u ^ (n - p) := by rw [← pow_add]; congr 1; omega
    have h1 : u ^ (n - p) ≤ 2 ^ (n - p) * e ^ (n - p) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hu0 hu2 _
    have h2 : (2 : ℝ) ^ (n - p) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    rcases le_total n (3 * p) with hn3 | hn3
    · have h3 : e ^ (n - p) ≤ e ^ (2 * p) := pow_le_pow_right₀ he (by omega)
      rw [e1]
      calc Nr ^ ((2 : ℝ) - n / 2) * (u ^ (2 * p) * u ^ (n - p))
          ≤ 1 * (u ^ (2 * p) * (2 ^ n * e ^ (2 * p))) := by
            refine mul_le_mul hr1 ?_ (by positivity) zero_le_one
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
            exact mul_le_mul h2 h3 (by positivity) (by positivity)
        _ = _ := by ring
    · have h3 : e ^ (n - p) ≤ e ^ (2 * p) * Nr ^ (n - 3 * p) := by
        rw [show n - p = 2 * p + (n - 3 * p) by omega, pow_add]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) heN _) (by positivity)
      have h4 : Nr ^ ((2 : ℝ) - n / 2) * Nr ^ (n - 3 * p) ≤ 1 := by
        rw [show (Nr ^ (n - 3 * p) : ℝ) = Nr ^ (((n - 3 * p : ℕ) : ℝ)) by rw [Real.rpow_natCast],
          ← Real.rpow_add hN0]
        refine Real.rpow_le_one_of_one_le_of_nonpos hN ?_
        have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
        have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
        rw [Nat.cast_sub hn3]; push_cast
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp
        linarith
      rw [e1]
      calc Nr ^ ((2 : ℝ) - n / 2) * (u ^ (2 * p) * u ^ (n - p))
          ≤ Nr ^ ((2 : ℝ) - n / 2) *
              (u ^ (2 * p) * (2 ^ n * (e ^ (2 * p) * Nr ^ (n - 3 * p)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hr0
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
            exact mul_le_mul h2 h3 (by positivity) (by positivity)
        _ = (Nr ^ ((2 : ℝ) - n / 2) * Nr ^ (n - 3 * p)) * (2 ^ n * e ^ (2 * p) * u ^ (2 * p)) := by
            ring
        _ ≤ 1 * (2 ^ n * e ^ (2 * p) * u ^ (2 * p)) := by gcongr
        _ = _ := one_mul _

/-- The exponent count for `u = eΨ > 1` at `n = 3`, when `N ≤ e⁴`. -/
private lemma aw_exp_II3 {Nr e u : ℝ} (hN : 1 ≤ Nr) (he : 1 ≤ e) (hNe : Nr ≤ e ^ 4)
    (hu1 : 1 ≤ u) (hu2 : u ≤ 2 * e) {p : ℕ} (hp : 2 ≤ p) :
    Nr ^ ((2 : ℝ) - (3 : ℕ) / 2) * u ^ (3 + p) ≤ 2 * e ^ (2 * p) * u ^ (2 * p) := by
  have hN0 : 0 < Nr := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hsq : Nr ^ ((2 : ℝ) - (3 : ℕ) / 2) ≤ e ^ 2 := by
    rw [show ((2 : ℝ) - (3 : ℕ) / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_le_left (by positivity)]
    calc Nr ≤ e ^ 4 := hNe
      _ = (e ^ 2) ^ 2 := by ring
  have hr0 : 0 ≤ Nr ^ ((2 : ℝ) - (3 : ℕ) / 2) := Real.rpow_nonneg hN0.le _
  rcases Nat.lt_or_ge p 3 with hp3 | hp3
  · have hp2' : p = 2 := by omega
    subst hp2'
    calc Nr ^ ((2 : ℝ) - (3 : ℕ) / 2) * u ^ (3 + 2) ≤ e ^ 2 * (u ^ 4 * (2 * e)) := by
          rw [show u ^ (3 + 2) = u ^ 4 * u by ring]
          exact mul_le_mul hsq (mul_le_mul_of_nonneg_left hu2 (by positivity)) (by positivity)
            (by positivity)
      _ = 2 * e ^ 3 * u ^ 4 := by ring
      _ ≤ 2 * e ^ (2 * 2) * u ^ (2 * 2) := by
          have : e ^ 3 ≤ e ^ 4 := pow_le_pow_right₀ he (by norm_num)
          norm_num
          nlinarith [pow_nonneg hu0 4]
  · have h1 : u ^ (3 + p) ≤ u ^ (2 * p) := pow_le_pow_right₀ hu1 (by omega)
    have h2 : e ^ 2 ≤ e ^ (2 * p) := pow_le_pow_right₀ he (by omega)
    calc Nr ^ ((2 : ℝ) - (3 : ℕ) / 2) * u ^ (3 + p) ≤ e ^ (2 * p) * u ^ (2 * p) :=
          mul_le_mul (hsq.trans h2) h1 (by positivity) (by positivity)
      _ ≤ 2 * e ^ (2 * p) * u ^ (2 * p) := by
          have : 0 ≤ e ^ (2 * p) * u ^ (2 * p) := by positivity
          linarith

end Entry

/-! ## The cases of the coefficient bound at a fixed matrix -/

section Cases

variable {N : ℕ}

/-- Case `εa > 1` (deterministic): `N^{−n/2} |∑ s f_n| ≤ C (D Ψ²)^p` for `D ≥ N⁴`. -/
private lemma aw_caseI {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {z : ℂ} (hz : 0 < z.im)
    (hηN : 1 ≤ N * z.im) (hηT : z.im ≤ τ⁻¹) {D : ℝ} (hD : (N : ℝ) ^ 4 ≤ D)
    {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) {p n : ℕ} (hp : 2 ≤ p) (hn : n ≤ 4 * p) :
    (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      (4 * p + 1) ^ p * 4 ^ (4 * p) * ((1 + τ⁻¹) ^ p + 1) * τ⁻¹ ^ p *
        (D * PsiW (specOf A) z ^ 2) ^ p := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT1 : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
  obtain ⟨hp1, -, -⟩ := aw_psi (a := specOf A) hN hz
  have hηi0 : 0 < z.im⁻¹ := inv_pos.2 hz
  have hTη : 1 ≤ τ⁻¹ * z.im⁻¹ := by rw [← div_eq_mul_inv, one_le_div hz]; exact hηT
  set C := (4 * (p : ℝ) + 1) ^ p * 4 ^ (4 * p) * ((1 + τ⁻¹) ^ p + 1) with hC
  have hC0 : 0 ≤ C := by positivity
  have hM : ∀ α : UpperIdx N, ‖fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      C * z.im⁻¹ ^ (n + p) := fun α => by
    refine (aw_det_fCoeff hN hA hW hz α.1.1 α.1.2 p n).trans ?_
    have h1 : ((n : ℝ) + 1) ^ p ≤ (4 * p + 1) ^ p := by
      have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
      exact pow_le_pow_left₀ (by positivity) (by linarith) p
    have h2 : (4 * z.im⁻¹) ^ n ≤ 4 ^ (4 * p) * z.im⁻¹ ^ n := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (by positivity)
    have h3 : (z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p ≤ ((1 + τ⁻¹) ^ p + 1) * z.im⁻¹ ^ p := by
      have : z.im⁻¹ + 1 ≤ (1 + τ⁻¹) * z.im⁻¹ := by nlinarith
      have := pow_le_pow_left₀ (by positivity) this p
      rw [mul_pow] at this
      linarith
    calc ((n : ℝ) + 1) ^ p * ((4 * z.im⁻¹) ^ n * ((z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p))
        ≤ (4 * p + 1) ^ p * ((4 ^ (4 * p) * z.im⁻¹ ^ n) * (((1 + τ⁻¹) ^ p + 1) * z.im⁻¹ ^ p)) := by
          gcongr
      _ = C * z.im⁻¹ ^ (n + p) := by rw [hC, pow_add]; ring
  have hsum := aw_sum_entries hs _ (by positivity) hM
  have hexp := aw_exp_I hNr hz hηN hηT hT1 hD hp hn
  have hpsi : D * (1 / (N * z.im)) ^ 2 ≤ D * PsiW (specOf A) z ^ 2 := by
    have hD0 : 0 ≤ D := le_trans (by positivity) hD
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp1 2) hD0
  calc (N : ℝ) ^ (-(n : ℝ) / 2) *
        ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖
      ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ((N : ℝ) ^ 2 * (C * z.im⁻¹ ^ (n + p))) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hN0.le _)
    _ = C * ((N : ℝ) ^ ((2 : ℝ) - n / 2) * z.im⁻¹ ^ (n + p)) := by
        rw [← aw_rpow_n2 hN0 n]; ring
    _ ≤ C * (τ⁻¹ ^ p * (D * (1 / (N * z.im)) ^ 2) ^ p) := mul_le_mul_of_nonneg_left hexp hC0
    _ ≤ C * (τ⁻¹ ^ p * (D * PsiW (specOf A) z ^ 2) ^ p) := by
        gcongr
        exact mul_nonneg (le_trans (by positivity) hD) (by positivity)
    _ = _ := by rw [hC]; ring

/-- Case `u = eΨ > 1`, `e ≤ N`, on the event. -/
private lemma aw_caseII {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im) (hηN : 1 ≤ N * z.im) {κ e D : ℝ} (hκ : 0 < κ)
    (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) (heN : e ≤ N) (hD : e ^ 4 ≤ D)
    (hu1 : 1 ≤ e * PsiW (specOf A) z) {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) {p n : ℕ}
    (hp : 2 ≤ p) (hn3 : 3 ≤ n) (hn : n ≤ 4 * p) (h3 : n = 3 → (N : ℝ) ≤ e ^ 4)
    (hE : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      e * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) * testNorm (awVec s (piW A z) l)) :
    (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      (4 * p + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) *
        (1 + (2 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1)) ^ p) * 2 ^ (4 * p) *
        (D * PsiW (specOf A) z ^ 2) ^ p := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hp1, -, hp3⟩ := aw_psi (a := specOf A) hN hz
  have hΨ2 := hp3 hηN
  have hΨ0 : 0 ≤ PsiW (specOf A) z := le_trans (by positivity) hp1
  have ev := aw_mkEv hN hA hW hτ hS hzS hz hκ hIm he hs hE false
  set Ψ := PsiW (specOf A) z with hΨ
  set T := τ⁻¹ with hT
  set c₁ := 2 * T ^ 2 * (1 + κ⁻¹) + 1 with hc₁
  set u := e * Ψ with hu
  have hT0 : 0 ≤ T := inv_nonneg.2 hτ.le
  have hc0 : 0 ≤ c₁ := by have := inv_pos.2 hκ; positivity
  have hu0 : 0 ≤ u := by linarith
  have hB : ∀ a b, ‖GW A Wm z a b‖ ≤ (T + 1) * u := fun a b => by
    have := ev.bdd a b
    nlinarith
  have hB1 : 1 ≤ (T + 1) * u := by nlinarith
  have hℓ2 : Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 = c₁ * e * N * Ψ ^ 2 :=
    Real.sq_sqrt (by have := hc0; positivity)
  have hy : Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 / N ≤ 2 * c₁ * u := by
    rw [hℓ2, div_le_iff₀ hN0, hu]
    have : c₁ * e * Ψ * Ψ ≤ c₁ * e * Ψ * 2 := by
      have : 0 ≤ c₁ * e * Ψ := by have := hc0; positivity
      exact mul_le_mul_of_nonneg_left hΨ2 this
    nlinarith
  have hF : FtW A Wm z ≤ u := aw_FtW_le_u hN hA hz ev.tilde
  set C := (4 * (p : ℝ) + 1) ^ p * (4 * (T + 1)) ^ (4 * p) * (1 + (2 * c₁) ^ p) with hC
  have hC0 : 0 ≤ C := by positivity
  have hM : ∀ α : UpperIdx N, ‖fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      C * u ^ (n + p) := fun α => by
    have h0 : ‖avgCoeffW A Wm z α.1.1 α.1.2 0‖ ≤ u := by
      rw [aw_avgCoeff_zero]; exact hF
    refine (aw_entry_fCoeff hB1 hB ev.H_le hu0 α.1.1 α.1.2 h0 p n).trans ?_
    have h1 : ((n : ℝ) + 1) ^ p ≤ (4 * p + 1) ^ p := by
      have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
      exact pow_le_pow_left₀ (by positivity) (by linarith) p
    have h2 : (4 * ((T + 1) * u)) ^ n ≤ (4 * (T + 1)) ^ (4 * p) * u ^ n := by
      rw [show 4 * ((T + 1) * u) = (4 * (T + 1)) * u by ring, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hn) (by positivity)
    have h3' : u ^ p + (Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 / N) ^ p ≤
        (1 + (2 * c₁) ^ p) * u ^ p := by
      have := pow_le_pow_left₀ (by positivity) hy p
      rw [mul_pow] at this
      linarith
    calc ((n : ℝ) + 1) ^ p * ((4 * ((T + 1) * u)) ^ n *
          (u ^ p + (Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 / N) ^ p))
        ≤ (4 * p + 1) ^ p * (((4 * (T + 1)) ^ (4 * p) * u ^ n) * ((1 + (2 * c₁) ^ p) * u ^ p)) := by
          gcongr
      _ = C * u ^ (n + p) := by rw [hC, pow_add]; ring
  have hsum := aw_sum_entries hs _ (by positivity) hM
  have hu2 : u ≤ 2 * e := by
    have := mul_le_mul_of_nonneg_left hΨ2 (by linarith : (0 : ℝ) ≤ e)
    rw [hu]; linarith
  have hexp : (N : ℝ) ^ ((2 : ℝ) - n / 2) * u ^ (n + p) ≤
      2 ^ (4 * p) * e ^ (2 * p) * u ^ (2 * p) := by
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · have hn3' : n = 3 := by omega
      have := aw_exp_II3 hNr he (h3 hn3') hu1 hu2 hp
      rw [hn3']
      refine this.trans ?_
      have : (2 : ℝ) ≤ 2 ^ (4 * p) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
      have : 0 ≤ e ^ (2 * p) * u ^ (2 * p) := by positivity
      nlinarith
    · have := aw_exp_II hNr he heN hu1 hu2 hp hn4 hn
      refine this.trans ?_
      have : (2 : ℝ) ^ n ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) hn
      have : 0 ≤ e ^ (2 * p) * u ^ (2 * p) := by positivity
      nlinarith
  have hfin : e ^ (2 * p) * u ^ (2 * p) ≤ (D * Ψ ^ 2) ^ p := by
    have e1 : e ^ (2 * p) * u ^ (2 * p) = (e ^ 4 * Ψ ^ 2) ^ p := by
      rw [hu, pow_mul, pow_mul, ← mul_pow]; ring
    rw [e1]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hD (sq_nonneg Ψ)) p
  calc (N : ℝ) ^ (-(n : ℝ) / 2) *
        ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖
      ≤ (N : ℝ) ^ (-(n : ℝ) / 2) * ((N : ℝ) ^ 2 * (C * u ^ (n + p))) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hN0.le _)
    _ = C * ((N : ℝ) ^ ((2 : ℝ) - n / 2) * u ^ (n + p)) := by
        rw [← aw_rpow_n2 hN0 n]; ring
    _ ≤ C * (2 ^ (4 * p) * e ^ (2 * p) * u ^ (2 * p)) := mul_le_mul_of_nonneg_left hexp hC0
    _ = C * 2 ^ (4 * p) * (e ^ (2 * p) * u ^ (2 * p)) := by ring
    _ ≤ C * 2 ^ (4 * p) * (D * Ψ ^ 2) ^ p := by gcongr
    _ = _ := by rw [hC]


/-- Case `u = eΨ ≤ 1`, `n ≥ 4`, on the event. -/
private lemma aw_caseIIIa {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im) {κ e D : ℝ} (hκ : 0 < κ)
    (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) (hD : e ^ 4 ≤ D)
    (hu : e * PsiW (specOf A) z ≤ 1) {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) {p n : ℕ}
    (hn4 : 4 ≤ n) (hn : n ≤ 4 * p)
    (hE : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      e * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) * testNorm (awVec s (piW A z) l)) :
    (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      (4 * p + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) *
        (FtW A Wm z ^ p + (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ p * (D * PsiW (specOf A) z ^ 2) ^ p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hp1, -, -⟩ := aw_psi (a := specOf A) hN hz
  have hΨ0 : 0 ≤ PsiW (specOf A) z := le_trans (by positivity) hp1
  have ev := aw_mkEv hN hA hW hτ hS hzS hz hκ hIm he hs hE false
  set Ψ := PsiW (specOf A) z with hΨ
  set T := τ⁻¹ with hT
  set c₁ := 2 * T ^ 2 * (1 + κ⁻¹) + 1 with hc₁
  have hT0 : 0 ≤ T := inv_nonneg.2 hτ.le
  have hc0 : 0 ≤ c₁ := by have := inv_pos.2 hκ; positivity
  have hB : ∀ a b, ‖GW A Wm z a b‖ ≤ T + 1 := fun a b => by
    have := ev.bdd a b; linarith
  have hℓ2 : Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 = c₁ * e * N * Ψ ^ 2 :=
    Real.sq_sqrt (by have := hc0; positivity)
  have hy : Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 / N ≤ c₁ * (D * Ψ ^ 2) := by
    rw [hℓ2, div_le_iff₀ hN0]
    have heD : e ≤ D := (le_self_pow₀ he (by norm_num)).trans hD
    have : c₁ * e * Ψ ^ 2 ≤ c₁ * D * Ψ ^ 2 := by gcongr
    nlinarith
  set C := (4 * (p : ℝ) + 1) ^ p * (4 * (T + 1)) ^ (4 * p) with hC
  have hC0 : 0 ≤ C := by positivity
  have hM : ∀ α : UpperIdx N, ‖fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      C * (FtW A Wm z ^ p + c₁ ^ p * (D * Ψ ^ 2) ^ p) := fun α => by
    have h0 : ‖avgCoeffW A Wm z α.1.1 α.1.2 0‖ ≤ FtW A Wm z := by rw [aw_avgCoeff_zero]; rfl
    refine (aw_entry_fCoeff (by linarith) hB ev.H_le (norm_nonneg _) α.1.1 α.1.2 h0 p n).trans ?_
    have h1 : ((n : ℝ) + 1) ^ p ≤ (4 * p + 1) ^ p := by
      have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
      exact pow_le_pow_left₀ (by positivity) (by linarith) p
    have h2 : (4 * (T + 1)) ^ n ≤ (4 * (T + 1)) ^ (4 * p) := pow_le_pow_right₀ (by linarith) hn
    have h3 : (Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 / N) ^ p ≤ c₁ ^ p * (D * Ψ ^ 2) ^ p := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hy p
    have hF0 : 0 ≤ FtW A Wm z := norm_nonneg _
    calc ((n : ℝ) + 1) ^ p * ((4 * (T + 1)) ^ n *
          (FtW A Wm z ^ p + (Real.sqrt (c₁ * e * N * Ψ ^ 2) ^ 2 / N) ^ p))
        ≤ (4 * p + 1) ^ p * ((4 * (T + 1)) ^ (4 * p) *
          (FtW A Wm z ^ p + c₁ ^ p * (D * Ψ ^ 2) ^ p)) := by gcongr
      _ = _ := by rw [hC]; ring
  have hQ0 : 0 ≤ C * (FtW A Wm z ^ p + c₁ ^ p * (D * Ψ ^ 2) ^ p) := by
    have : 0 ≤ D * Ψ ^ 2 := by
      have : 0 ≤ D := le_trans (by positivity) hD
      positivity
    have : 0 ≤ FtW A Wm z := norm_nonneg _
    positivity
  have hsum := aw_sum_entries hs _ hQ0 hM
  have hr : (N : ℝ) ^ ((2 : ℝ) - n / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hNr ?_
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  calc (N : ℝ) ^ (-(n : ℝ) / 2) *
        ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖
      ≤ (N : ℝ) ^ (-(n : ℝ) / 2) *
          ((N : ℝ) ^ 2 * (C * (FtW A Wm z ^ p + c₁ ^ p * (D * Ψ ^ 2) ^ p))) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ ((2 : ℝ) - n / 2) * (C * (FtW A Wm z ^ p + c₁ ^ p * (D * Ψ ^ 2) ^ p)) := by
        rw [← aw_rpow_n2 hN0 n]; ring
    _ ≤ 1 * (C * (FtW A Wm z ^ p + c₁ ^ p * (D * Ψ ^ 2) ^ p)) :=
        mul_le_mul_of_nonneg_right hr hQ0
    _ = _ := by rw [one_mul, hC]

/-- The deterministic bound off the event: `N^{−n/2} |∑ s f_n| ≤ C N^{2 + 5p}`. -/
private lemma aw_off {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : 1 ≤ N * z.im) {s : UpperIdx N → ℂ}
    (hs : ∀ α, ‖s α‖ ≤ 1) {p n : ℕ} (hn : n ≤ 4 * p) :
    (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      (4 * p + 1) ^ p * 4 ^ (4 * p) * 2 ^ (p + 1) * (N : ℝ) ^ (2 + 5 * p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hηi : z.im⁻¹ ≤ N := by rw [inv_le_iff_one_le_mul₀ hz]; linarith
  have hηi0 : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  set C := (4 * (p : ℝ) + 1) ^ p * 4 ^ (4 * p) * 2 ^ (p + 1) with hC
  have hM : ∀ α : UpperIdx N, ‖fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      C * (N : ℝ) ^ (5 * p) := fun α => by
    refine (aw_det_fCoeff hN hA hW hz α.1.1 α.1.2 p n).trans ?_
    have h1 : ((n : ℝ) + 1) ^ p ≤ (4 * p + 1) ^ p := by
      have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
      exact pow_le_pow_left₀ (by positivity) (by linarith) p
    have h2 : (4 * z.im⁻¹) ^ n ≤ 4 ^ (4 * p) * (N : ℝ) ^ (4 * p) := by
      rw [← mul_pow]
      calc (4 * z.im⁻¹) ^ n ≤ (4 * (N : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
        _ ≤ (4 * (N : ℝ)) ^ (4 * p) := pow_le_pow_right₀ (by nlinarith) hn
    have h3 : (z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p ≤ 2 ^ (p + 1) * (N : ℝ) ^ p := by
      have a1 : (z.im⁻¹ + 1) ^ p ≤ (2 * (N : ℝ)) ^ p :=
        pow_le_pow_left₀ (by positivity) (by linarith) p
      have a2 : z.im⁻¹ ^ p ≤ (N : ℝ) ^ p := pow_le_pow_left₀ hηi0 hηi p
      have a3 : (N : ℝ) ^ p ≤ 2 ^ p * (N : ℝ) ^ p := le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num))
      rw [mul_pow] at a1
      rw [pow_succ]
      linarith
    calc ((n : ℝ) + 1) ^ p * ((4 * z.im⁻¹) ^ n * ((z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p))
        ≤ (4 * p + 1) ^ p * ((4 ^ (4 * p) * (N : ℝ) ^ (4 * p)) * (2 ^ (p + 1) * (N : ℝ) ^ p)) := by
          gcongr
      _ = C * (N : ℝ) ^ (5 * p) := by
          rw [hC, show 5 * p = 4 * p + p by ring, pow_add]; ring
  have hsum := aw_sum_entries hs _ (by positivity) hM
  have hr : (N : ℝ) ^ (-(n : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hNr ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc (N : ℝ) ^ (-(n : ℝ) / 2) *
        ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖
      ≤ 1 * ((N : ℝ) ^ 2 * (C * (N : ℝ) ^ (5 * p))) :=
        mul_le_mul hr hsum (norm_nonneg _) zero_le_one
    _ = C * (N : ℝ) ^ (2 + 5 * p) := by rw [pow_add]; ring

/-- The constant of the bound on the event. -/
private def awK (τ κ : ℝ) (p : ℕ) : ℝ :=
  (4 * p + 1) ^ p * 4 ^ (4 * p) * ((1 + τ⁻¹) ^ p + 1) * τ⁻¹ ^ p +
    (4 * p + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) *
      (1 + (2 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1)) ^ p) * 2 ^ (4 * p) +
    (4 * p + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) * (1 + (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ p) +
    4 ^ p * (1 + (100 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ 3 * (τ⁻¹ + 1) ^ 2) ^ p * 2 ^ p)

private lemma aw_add_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p : ℕ) :
    (x + y) ^ p ≤ 2 ^ p * (x ^ p + y ^ p) := by
  rcases le_total x y with h | h
  · calc (x + y) ^ p ≤ (2 * y) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * y ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := by
          gcongr; exact le_add_of_nonneg_left (pow_nonneg hx _)
  · calc (x + y) ^ p ≤ (2 * x) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * x ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := by
          gcongr; exact le_add_of_nonneg_right (pow_nonneg hy _)

private lemma aw_awK_ge {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (p : ℕ) :
    (4 * p + 1) ^ p * 4 ^ (4 * p) * ((1 + τ⁻¹) ^ p + 1) * τ⁻¹ ^ p ≤ awK τ κ p ∧
    (4 * p + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) *
      (1 + (2 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1)) ^ p) * 2 ^ (4 * p) ≤ awK τ κ p ∧
    (4 * p + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) * (1 + (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ p) ≤
      awK τ κ p ∧
    4 ^ p * (1 + (100 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ 3 * (τ⁻¹ + 1) ^ 2) ^ p * 2 ^ p) ≤
      awK τ κ p := by
  have hT0 : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
  have hκ0 : 0 ≤ κ⁻¹ := (inv_pos.2 hκ).le
  have h1 : 0 ≤ (4 * (p : ℝ) + 1) ^ p * 4 ^ (4 * p) * ((1 + τ⁻¹) ^ p + 1) * τ⁻¹ ^ p := by
    positivity
  have h2 : 0 ≤ (4 * (p : ℝ) + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) *
      (1 + (2 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1)) ^ p) * 2 ^ (4 * p) := by positivity
  have h3 : 0 ≤ (4 * (p : ℝ) + 1) ^ p * (4 * (τ⁻¹ + 1)) ^ (4 * p) *
      (1 + (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ p) := by positivity
  have h4 : 0 ≤ (4 : ℝ) ^ p * (1 + (100 * (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ 3 * (τ⁻¹ + 1) ^ 2) ^ p *
      2 ^ p) := by positivity
  unfold awK
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- `L ≤ c Q`, `c ≤ K`, `0 ≤ Q ≤ R` give `L ≤ K R`. -/
private lemma aw_fin {L K c Q R : ℝ} (h : L ≤ c * Q) (hcK : c ≤ K) (hc : 0 ≤ c) (hQ : 0 ≤ Q)
    (hQR : Q ≤ R) : L ≤ K * R :=
  h.trans ((mul_le_mul_of_nonneg_left hQR hc).trans
    (mul_le_mul_of_nonneg_right hcK (hQ.trans hQR)))

/-- `L ≤ C (F + c X)` with `c ≥ 1` gives `L ≤ C (1 + c) (X + b + F)`. -/
private lemma aw_finIII {L C c X b F K : ℝ} (h : L ≤ C * (F + c * X)) (hC : 0 ≤ C) (hc : 1 ≤ c)
    (hX : 0 ≤ X) (hb : 0 ≤ b) (hF : 0 ≤ F) (hK : C * (1 + c) ≤ K) : L ≤ K * (X + b + F) := by
  have h1 : F + c * X ≤ (1 + c) * (X + b + F) := by
    have e : (1 + c) * (X + b + F) = F + c * X + (X + (1 + c) * b + c * F) := by ring
    have : 0 ≤ X + (1 + c) * b + c * F := by
      have : 0 ≤ (1 + c) * b := mul_nonneg (by linarith) hb
      have : 0 ≤ c * F := mul_nonneg (by linarith) hF
      linarith
    linarith
  have hR : 0 ≤ X + b + F := by linarith
  calc L ≤ C * (F + c * X) := h
    _ ≤ C * ((1 + c) * (X + b + F)) := mul_le_mul_of_nonneg_left h1 hC
    _ = C * (1 + c) * (X + b + F) := by ring
    _ ≤ K * (X + b + F) := mul_le_mul_of_nonneg_right hK hR

private lemma aw_N32 {Nr : ℝ} (hN : 0 < Nr) :
    Nr ^ (-((3 : ℕ) : ℝ) / 2) * (Nr * Real.sqrt Nr) = 1 := by
  rw [Real.sqrt_eq_rpow, show (Nr * Nr ^ (1 / 2 : ℝ)) = Nr ^ (3 / 2 : ℝ) by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one],
    ← Real.rpow_add hN]
  norm_num

/-- The order-three bound rescaled: `N^{−3/2} · 4^p N^{3/2} (F + (K₀(X+b))^p) ≤ C₃ (X^p+b^p+F)`. -/
private lemma aw_fin3 {Nr L F X b K₀ : ℝ} (hN : 0 < Nr) {p : ℕ} (hF : 0 ≤ F) (hX : 0 ≤ X)
    (hb : 0 ≤ b) (hK : 0 ≤ K₀)
    (h : L ≤ 4 ^ p * ((Nr * Real.sqrt Nr) * (F + (K₀ * (X + b)) ^ p))) :
    Nr ^ (-((3 : ℕ) : ℝ) / 2) * L ≤ 4 ^ p * (1 + K₀ ^ p * 2 ^ p) * (X ^ p + b ^ p + F) := by
  have hXb := aw_add_pow_le hX hb p
  calc Nr ^ (-((3 : ℕ) : ℝ) / 2) * L
      ≤ Nr ^ (-((3 : ℕ) : ℝ) / 2) * (4 ^ p * ((Nr * Real.sqrt Nr) * (F + (K₀ * (X + b)) ^ p))) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hN.le _)
    _ = (Nr ^ (-((3 : ℕ) : ℝ) / 2) * (Nr * Real.sqrt Nr)) *
          (4 ^ p * (F + K₀ ^ p * (X + b) ^ p)) := by
        rw [mul_pow]; ring
    _ = 4 ^ p * (F + K₀ ^ p * (X + b) ^ p) := by rw [aw_N32 hN, one_mul]
    _ ≤ 4 ^ p * (F + K₀ ^ p * (2 ^ p * (X ^ p + b ^ p))) := by gcongr
    _ ≤ 4 ^ p * (1 + K₀ ^ p * 2 ^ p) * (X ^ p + b ^ p + F) := by
        have h0 : 0 ≤ K₀ ^ p * 2 ^ p := by positivity
        have h1 : 0 ≤ X ^ p + b ^ p := by positivity
        have e1 : 4 ^ p * (1 + K₀ ^ p * 2 ^ p) * (X ^ p + b ^ p + F) =
            4 ^ p * (F + K₀ ^ p * (2 ^ p * (X ^ p + b ^ p))) +
              4 ^ p * ((X ^ p + b ^ p) + K₀ ^ p * 2 ^ p * F) := by ring
        rw [e1]
        have : 0 ≤ (4 : ℝ) ^ p * ((X ^ p + b ^ p) + K₀ ^ p * 2 ^ p * F) := by positivity
        linarith

/-- The bound on the event: `N^{−n/2} |∑ s f_n| ≤ K ((DΨ²)^p + (β/(Nη))^p + F̃^p)`. -/
private lemma aw_on_event {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {S : Set ℂ}
    (hS : StandingBoundW τ (specOf A) S) {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im)
    (hηN : 1 ≤ N * z.im) (hηT : z.im ≤ τ⁻¹) {κ e D β : ℝ} (hκ : 0 < κ)
    (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) (hD : e ^ 4 ≤ D)
    (hcase : (N : ℝ) ^ 4 ≤ D ∨ e ≤ N) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) {p n : ℕ} (hp : 2 ≤ p) (hn3 : 3 ≤ n)
    (hn : n ≤ 4 * p)
    (h3a : n = 3 → (N : ℝ) * PsiW (specOf A) z ^ 2 ≤ Real.sqrt N * β ^ 4)
    (h3b : n = 3 → 1 ≤ e * PsiW (specOf A) z → (N : ℝ) ≤ e ^ 4)
    (hE : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      e * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) * testNorm (awVec s (piW A z) l)) :
    (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      awK τ κ p * ((D * PsiW (specOf A) z ^ 2) ^ p + (β / (N * z.im)) ^ p + FtW A Wm z ^ p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hT0 : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
  have hκ0 : 0 ≤ κ⁻¹ := (inv_pos.2 hκ).le
  have hXp0 : 0 ≤ (D * PsiW (specOf A) z ^ 2) ^ p := by positivity
  have hbp0 : 0 ≤ (β / (N * z.im)) ^ p := by positivity
  have hFp0 : 0 ≤ FtW A Wm z ^ p := pow_nonneg (norm_nonneg _) p
  obtain ⟨kI, kII, kIII, k3⟩ := aw_awK_ge hτ hκ p
  rcases hcase with hN4 | heN
  · exact aw_fin (aw_caseI hN hA hW hτ hτ1 hz hηN hηT hN4 hs hp hn) kI (by positivity) hXp0
      (by linarith)
  by_cases hu1 : 1 ≤ e * PsiW (specOf A) z
  · exact aw_fin (aw_caseII hN hA hW hτ hS hzS hz hηN hκ hIm he heN hD hu1 hs hp hn3 hn
      (fun h' => h3b h' hu1) hE) kII (by positivity) hXp0 (by linarith)
  have hu : e * PsiW (specOf A) z ≤ 1 := (not_le.1 hu1).le
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · have hn3' : n = 3 := by omega
    subst hn3'
    have h := aw_case3 hN hA hW hτ hτ1 hS hzS hz hκ hIm he hD hβ0 hβ1 hu (h3a rfl) hs p hE
    have h' := aw_fin3 hN0 (norm_nonneg _ |> pow_nonneg <| p) (by positivity) (by positivity)
      (by positivity) h
    refine h'.trans (mul_le_mul_of_nonneg_right k3 (by positivity))
  · have h := aw_caseIIIa hN hA hW hτ hS hzS hz hκ hIm he hD hu hs hn4 hn hE
    have hc1 : (1 : ℝ) ≤ (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) ^ p := one_le_pow₀ (by
      have : 0 ≤ 2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) := by positivity
      linarith)
    exact aw_finIII h (by positivity) hc1 hXp0 hbp0 hFp0 kIII

end Cases

/-! ## Measurability in `W` -/

section Meas

variable {N : ℕ}

private lemma aw_measurable_GW {Ω : Type*} [MeasurableSpace Ω] {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : ∀ i j, Measurable fun ω => W ω i j) (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun ω => GW A (W ω) z := by
  set M : Ω → Matrix (Fin N) (Fin N) ℂ :=
    fun ω => cplx (W ω + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hMdef
  have hM : Measurable M := by
    refine Matrix.measurable_iff.2 fun a b => ?_
    simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, cplx, Matrix.map_apply,
      Matrix.add_apply]
    refine Measurable.sub ?_ measurable_const
    exact Complex.measurable_ofReal.comp (((hW a b).add measurable_const))
  have h : (fun ω => GW A (W ω) z) = fun ω => (M ω).det⁻¹ • (M ω).adjugate := by
    funext ω
    change (M ω)⁻¹ = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuous_id.matrix_det).measurable.comp hM).inv.smul
    ((continuous_id.matrix_adjugate).measurable.comp hM)

private lemma aw_continuous_fCoeff {X : Type*} [TopologicalSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Continuous fun x => a x k) :
    Continuous fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.comp (ha _)

/-- `ω ↦ f_n(a(W(ω)))` is measurable. -/
private lemma aw_measurable_fCoeff {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N) (p n : ℕ) :
    Measurable fun ω => fCoeff p (avgCoeffW A (W ω) z i j) n := by
  set Φ : Matrix (Fin N) (Fin N) ℂ → ℂ := fun M => fCoeff p (fun k =>
    (-1) ^ k * (N : ℂ)⁻¹ * trace (M * (deltaW i j * M) ^ k) -
      if k = 0 then mW (specOf A) z else 0) n with hΦ
  have hc : Continuous Φ := aw_continuous_fCoeff p n fun k =>
    (continuous_const.mul (continuous_id.matrix_mul
      ((continuous_const.matrix_mul continuous_id).pow k)).matrix_trace).sub continuous_const
  exact hc.measurable.comp (aw_measurable_GW hW A z)

/-- `ω ↦ F̃(W(ω))^p` is measurable. -/
private lemma aw_measurable_FtW {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (p : ℕ) :
    Measurable fun ω => FtW A (W ω) z ^ p := by
  have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℂ =>
      ‖(N : ℂ)⁻¹ * trace M - mW (specOf A) z‖ ^ p :=
    ((continuous_const.mul continuous_id.matrix_trace).sub continuous_const).norm.pow p
  exact hc.measurable.comp (aw_measurable_GW hW A z)

end Meas

/-! ## Splitting the expectation along the event -/

section Split

/-- If `0 ≤ Z ≤ g` on `Ξ` and `Z ≤ M` everywhere, then `E Z ≤ E g + M P(Ξᶜ)`. -/
private lemma aw_split_int {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Z g : Ω → ℝ} {Ξ : Set Ω} {M : ℝ} (hM : 0 ≤ M) (hZ0 : ∀ ω, 0 ≤ Z ω) (hgi : Integrable g)
    (hg0 : ∀ ω, 0 ≤ g ω) (hon : ∀ ω ∈ Ξ, Z ω ≤ g ω) (hoff : ∀ ω, Z ω ≤ M) :
    ∫ ω, Z ω ≤ (∫ ω, g ω) + M * (ℙ Ξᶜ).toReal := by
  set Bs : Set Ω := toMeasurable ℙ Ξᶜ with hBs
  have hpt : ∀ ω, Z ω ≤ g ω + Bs.indicator (fun _ => M) ω := by
    intro ω
    have hind : 0 ≤ Bs.indicator (fun _ => M) ω := Set.indicator_nonneg (fun _ _ => hM) _
    by_cases hω : ω ∈ Ξ
    · have := hon ω hω; linarith
    · have hmem : ω ∈ Bs := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hmem]
      linarith [hoff ω, hg0 ω]
  have hI : Integrable fun ω => Bs.indicator (fun _ => M) ω :=
    (integrable_const _).indicator (measurableSet_toMeasurable _ _)
  have h2 : Integrable fun ω => g ω + Bs.indicator (fun _ => M) ω := hgi.add hI
  have e1 : ∫ ω, (g ω + Bs.indicator (fun _ => M) ω) =
      (∫ ω, g ω) + ∫ ω, Bs.indicator (fun _ => M) ω := integral_add hgi hI
  have e3 : ∫ ω, Bs.indicator (fun _ => M) ω = (ℙ Ξᶜ).toReal * M := by
    rw [integral_indicator_const _ (measurableSet_toMeasurable _ _), measureReal_def,
      measure_toMeasurable, smul_eq_mul]
  calc ∫ ω, Z ω ≤ ∫ ω, (g ω + Bs.indicator (fun _ => M) ω) :=
        integral_mono_of_nonneg (ae_of_all _ hZ0) h2 (ae_of_all _ hpt)
    _ = _ := by rw [e1, e3]; ring


/-- Union bound for the event `Ξ` of the anisotropic bounds at all pairs of a finite family. -/
private lemma aw_prob {Ω : Type} [MeasureSpace Ω] {N : ℕ} {ι : Type} [Fintype ι]
    (V : ι → Fin N → ℝ) (F : Ω → Matrix (Fin N) (Fin N) ℂ) {ε Da Ψ : ℝ}
    (h : ODomMatAt N ε Da F (fun _ => Ψ)) :
    ℙ {ω | ∀ k l, ‖testBilin (V k) (F ω) (V l)‖ ≤
        (N : ℝ) ^ ε * (Ψ * testNorm (V k) * testNorm (V l))}ᶜ ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * (N : ℝ) ^ (-Da)) := by
  have hc : {ω | ∀ k l, ‖testBilin (V k) (F ω) (V l)‖ ≤
      (N : ℝ) ^ ε * (Ψ * testNorm (V k) * testNorm (V l))}ᶜ =
      ⋃ q : ι × ι, {ω | (N : ℝ) ^ ε * (Ψ * testNorm (V q.1) * testNorm (V q.2)) <
        ‖testBilin (V q.1) (F ω) (V q.2)‖} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, Set.mem_iUnion,
      Prod.exists]
  rw [hc]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hN0 : 0 ≤ (N : ℝ) ^ (-Da) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc ∑ q : ι × ι, ℙ {ω | (N : ℝ) ^ ε * (Ψ * testNorm (V q.1) * testNorm (V q.2)) <
        ‖testBilin (V q.1) (F ω) (V q.2)‖}
      ≤ ∑ _q : ι × ι, ENNReal.ofReal ((N : ℝ) ^ (-Da)) :=
        Finset.sum_le_sum fun q _ => h (V q.1) (V q.2)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * (N : ℝ) ^ (-Da)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [sq, ← Nat.cast_mul, ENNReal.ofReal_natCast]
end Split

/-! ## The pointwise bound in the setting of §12.2 -/

section Pointwise

/-- `(N^a)^k = N^{a k}`. -/
private lemma aw_rpow_pow {Nr : ℝ} (hN : 0 ≤ Nr) (a : ℝ) (k : ℕ) : (Nr ^ a) ^ k = Nr ^ (a * k) :=
  (Real.rpow_mul_natCast hN a k).symm

/-- In the setting of §12.2, at a matrix `Wm` on the event:
`N^{−n/2} |∑ s f_n| ≤ K ((N^δ Ψ²)^p + (N^{−c₀/2}/(Nη))^p + F̃^p)`. -/
private lemma aw_pointwise {τ c₀ δ εa : ℝ} {p : ℕ} (hc₀ : 0 < c₀) (hp2 : 2 ≤ p) (hεa : 0 < εa)
    (hεaδ : εa ≤ δ / 4) {N : ℕ} (hN : 1 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) {s : UpperIdx N → ℂ}
    (hs : ∀ α, ‖s α‖ ≤ 1) {n : ℕ} (hn : n ∈ Finset.Icc 3 (4 * p))
    (h3 : n = 3 → PsiSmallW c₀ (specOf A) S) {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
    (hE : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      (N : ℝ) ^ εa * (PsiW (specOf A) z * testNorm (awVec s (piW A z) k) *
        testNorm (awVec s (piW A z) l))) :
    (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A Wm z α.1.1 α.1.2) n‖ ≤
      awK τ ((3 * τ⁻¹ + 1) ^ 2)⁻¹ p * (((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p +
        ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p + FtW A Wm z ^ p) := by
  obtain ⟨hn3, hn4p⟩ := Finset.mem_Icc.1 hn
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hτ := hset.pos
  have hτ1 := hset.le_one
  have hA := hset.symmA
  have hzD := hset.domain.1 hz
  obtain ⟨hη, hre, hηlow, hηT⟩ := hzD
  have hηN : 1 ≤ (N : ℝ) * z.im := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    rw [Real.rpow_neg_one] at h1
    have := h1.trans hηlow
    rw [inv_le_iff_one_le_mul₀ hN0] at this
    linarith
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i => (abs_specOf_le_norm hA i).trans hset.normA
  have hIm := im_mW_ge hN hτ ha hη hre hηT
  have hκ : 0 < ((3 * τ⁻¹ + 1) ^ 2)⁻¹ := by
    have : 0 < τ⁻¹ := inv_pos.2 hτ
    positivity
  have he : 1 ≤ (N : ℝ) ^ εa := Real.one_le_rpow hNr hεa.le
  have hD : ((N : ℝ) ^ εa) ^ 4 ≤ (N : ℝ) ^ δ := by
    rw [aw_rpow_pow hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by push_cast; linarith)
  have hcase : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ δ ∨ (N : ℝ) ^ εa ≤ N := by
    by_cases hε1 : εa ≤ 1
    · right
      calc (N : ℝ) ^ εa ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr hε1
        _ = N := Real.rpow_one _
    · left
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by push_cast; linarith)
  have hβ0 : 0 < (N : ℝ) ^ (-c₀ / 2) := Real.rpow_pos_of_pos hN0 _
  have hβ1 : (N : ℝ) ^ (-c₀ / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  have hΨ0 : 0 ≤ PsiW (specOf A) z :=
    le_trans (by positivity) (aw_psi (a := specOf A) hN hη).1
  have h3a : n = 3 → (N : ℝ) * PsiW (specOf A) z ^ 2 ≤
      Real.sqrt N * ((N : ℝ) ^ (-c₀ / 2)) ^ 4 := fun h => by
    have hps := h3 h z hz
    have h2 : PsiW (specOf A) z ^ 2 ≤ ((N : ℝ) ^ (-1 / 4 - c₀)) ^ 2 :=
      pow_le_pow_left₀ hΨ0 hps 2
    rw [aw_rpow_pow hN0.le, Real.sqrt_eq_rpow]
    calc (N : ℝ) * PsiW (specOf A) z ^ 2 ≤ (N : ℝ) * (N : ℝ) ^ ((-1 / 4 - c₀) * ((2 : ℕ) : ℝ)) := by
          rw [← aw_rpow_pow hN0.le]; exact mul_le_mul_of_nonneg_left h2 hN0.le
      _ = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-c₀ / 2 * ((4 : ℕ) : ℝ)) := by
          have e : (N : ℝ) * (N : ℝ) ^ ((-1 / 4 - c₀) * ((2 : ℕ) : ℝ)) =
              (N : ℝ) ^ ((1 : ℝ) + (-1 / 4 - c₀) * ((2 : ℕ) : ℝ)) := by
            rw [Real.rpow_add hN0, Real.rpow_one]
          rw [e, ← Real.rpow_add hN0]
          congr 1; push_cast; ring
  have h3b : n = 3 → 1 ≤ (N : ℝ) ^ εa * PsiW (specOf A) z → (N : ℝ) ≤ ((N : ℝ) ^ εa) ^ 4 :=
    fun h hu => by
      have hps := h3 h z hz
      have h1 : PsiW (specOf A) z ≤ (N : ℝ) ^ (-1 / 4 : ℝ) :=
        hps.trans (Real.rpow_le_rpow_of_exponent_le hNr (by linarith))
      have h2 : 1 ≤ (N : ℝ) ^ εa * (N : ℝ) ^ (-1 / 4 : ℝ) :=
        hu.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
      have h4 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ εa := by
        have e1 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-1 / 4 : ℝ) = 1 := by
          rw [← Real.rpow_add hN0]; norm_num
        have hq : 0 < (N : ℝ) ^ (-1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
        nlinarith
      have h5 := pow_le_pow_left₀ (by positivity) h4 4
      rw [aw_rpow_pow hN0.le] at h5
      calc (N : ℝ) = (N : ℝ) ^ ((1 / 4 : ℝ) * ((4 : ℕ) : ℝ)) := by norm_num
        _ ≤ _ := h5
  have hE' : ∀ k l, ‖testBilin (awVec s (piW A z) k) (GW A Wm z - piW A z) (awVec s (piW A z) l)‖ ≤
      (N : ℝ) ^ εa * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) *
        testNorm (awVec s (piW A z) l) := fun k l => by
    have := hE k l; linarith [show (N : ℝ) ^ εa * (PsiW (specOf A) z *
      testNorm (awVec s (piW A z) k) * testNorm (awVec s (piW A z) l)) =
      (N : ℝ) ^ εa * PsiW (specOf A) z * testNorm (awVec s (piW A z) k) *
        testNorm (awVec s (piW A z) l) by ring]
  exact aw_on_event hN hA hW hτ hτ1 hset.standing hz hη hηN hηT hκ hIm he hD hcase hβ0 hβ1 hs hp2
    hn3 hn4p h3a h3b hE'

end Pointwise

/-- Lemma 12.8 (lowzYY), coefficient form, `n ∈ [3, 4p]` (for `n = 3` under (b), with the
deterministic weights `s`), at a single `z` where the anisotropic law holds for `W`. -/
theorem wig_avg_coeff (τ c₀ : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc₀ : 0 < c₀) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa)
    (hεaδ : εa ≤ δ / 4) (hDa : dPrev p ≤ Da) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WigSetting τ N A S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W →
        ∀ z ∈ S, AnisotropicLawWAt N εa Da A W {z} →
        ∀ (s : UpperIdx N → ℂ) (n : ℕ), (∀ α, ‖s α‖ ≤ 1) → n ∈ Finset.Icc 3 (4 * p) →
          (n = 3 → PsiSmallW c₀ (specOf A) S) →
          (N : ℝ) ^ (-(n : ℝ) / 2) *
            ‖∑ α : UpperIdx N, s α * ∫ ω, fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n‖ ≤
            K * (((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p
              + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p + ∫ ω, FtW A (W ω) z ^ p) := by
  have _hτ1 := hτ1
  have _hp := hp
  have hκ : 0 < ((3 * τ⁻¹ + 1) ^ 2)⁻¹ := by
    have : 0 < τ⁻¹ := inv_pos.2 hτ
    positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K : ℝ, K = awK τ ((3 * τ⁻¹ + 1) ^ 2)⁻¹ p := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]; exact le_trans (by positivity) (aw_awK_ge hτ hκ p).1
  obtain ⟨Cd, hCd⟩ : ∃ C : ℝ, C = (4 * (p : ℝ) + 1) ^ p * 4 ^ (4 * p) * 2 ^ (p + 1) := ⟨_, rfl⟩
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  refine ⟨K₁ + 81 * Cd * τ⁻¹ ^ (2 * p), by positivity, 1, ?_⟩
  intro N hN A S hset Ω _ _ W hW z hz hlaw s n hs hn h3
  obtain ⟨hn3, hn4p⟩ := Finset.mem_Icc.1 hn
  have hN1 : 1 ≤ N := hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hA := hset.symmA
  obtain ⟨hη, -, hηlow, hηT⟩ := hset.domain.1 hz
  have hηN : 1 ≤ (N : ℝ) * z.im := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    rw [Real.rpow_neg_one] at h1
    have := h1.trans hηlow
    rw [inv_le_iff_one_le_mul₀ hN0] at this
    linarith
  have hWs : ∀ ω, (W ω)ᵀ = W ω := hW.symm
  -- the event
  set Ψ := PsiW (specOf A) z with hΨ
  set V := awVec s (piW A z) with hV
  set Ξ : Set Ω := {ω | ∀ k l, ‖testBilin (V k) (GW A (W ω) z - piW A z) (V l)‖ ≤
      (N : ℝ) ^ εa * (Ψ * testNorm (V k) * testNorm (V l))} with hΞ
  have hP := aw_prob V (fun ω => GW A (W ω) z - piW A z) (hlaw z (Set.mem_singleton z))
  have hcard : (Fintype.card (Fin N ⊕ (Bool × Bool × Bool × Fin N)) : ℝ) = 9 * N := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    push_cast; ring
  rw [hcard] at hP
  have hPr : (ℙ Ξᶜ).toReal ≤ (9 * (N : ℝ)) ^ 2 * (N : ℝ) ^ (-Da) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hP
  -- integrability of the coefficients
  have hfm : ∀ α : UpperIdx N, Measurable fun ω => fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n :=
    fun α => aw_measurable_fCoeff hW.measurable A z _ _ p n
  have hfi : ∀ α : UpperIdx N,
      Integrable fun ω => fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n := fun α =>
    Integrable.of_bound (hfm α).aestronglyMeasurable _
      (ae_of_all _ fun ω => aw_det_fCoeff hN1 hA (hWs ω) hη α.1.1 α.1.2 p n)
  have hswap : ∑ α : UpperIdx N, s α * ∫ ω, fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n =
      ∫ ω, ∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n := by
    rw [integral_finsetSum _ fun α _ => (hfi α).const_mul (s α)]
    exact Finset.sum_congr rfl fun α _ => (integral_const_mul _ _).symm
  rw [hswap]
  -- `F̃^p` is integrable
  have hFm := aw_measurable_FtW hW.measurable A z p
  have hFi : Integrable fun ω => FtW A (W ω) z ^ p :=
    Integrable.of_bound hFm.aestronglyMeasurable ((z.im⁻¹ + 1) ^ p) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (show 0 ≤ FtW A (W ω) z from norm_nonneg _) p)]
      exact pow_le_pow_left₀ (norm_nonneg _) (aw_FtW_le hN1 hA (hWs ω) hη) p)
  set Xp := ((N : ℝ) ^ δ * Ψ ^ 2) ^ p with hXp
  set bp := ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p with hbp
  set EF := ∫ ω, FtW A (W ω) z ^ p with hEF
  have hXp0 : 0 ≤ Xp := by positivity
  have hbp0 : 0 ≤ bp := by positivity
  have hEF0 : 0 ≤ EF := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p
  -- the split along the event
  have hsplit := aw_split_int (Ξ := Ξ)
    (Z := fun ω => (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n‖)
    (g := fun ω => K₁ * (Xp + bp + FtW A (W ω) z ^ p))
    (M := Cd * (N : ℝ) ^ (2 + 5 * p)) (by positivity)
    (fun ω => by positivity)
    (((integrable_const _).add hFi).const_mul K₁)
    (fun ω => mul_nonneg hK₁0 (by have := pow_nonneg (norm_nonneg
      (mNW A (W ω) z - mW (specOf A) z)) p; unfold FtW; positivity))
    (fun ω hω => by
      have := aw_pointwise hc₀ hp2 hεa hεaδ hN1 hset hz hs hn h3 (hWs ω) hω
      rw [← hK₁] at this
      exact this)
    (fun ω => by
      have := aw_off hN1 hA (hWs ω) hη hηN hs hn4p (p := p) (n := n)
      rw [← hCd] at this
      exact this)
  have hint : ∫ ω, K₁ * (Xp + bp + FtW A (W ω) z ^ p) = K₁ * (Xp + bp + EF) := by
    rw [integral_const_mul, integral_add (integrable_const _) hFi, integral_const]
    simp [hEF]
  rw [hint] at hsplit
  -- the off-event term
  have hoffb : Cd * (N : ℝ) ^ (2 + 5 * p) * (ℙ Ξᶜ).toReal ≤ 81 * Cd * τ⁻¹ ^ (2 * p) * Xp := by
    have hΨτ : τ / N ≤ Ψ := by
      have h1 := (aw_psi (a := specOf A) hN1 hη).1
      refine le_trans ?_ h1
      rw [div_le_div_iff₀ hN0 (by positivity)]
      have := mul_le_mul_of_nonneg_left hηT hN0.le
      calc τ * (N * z.im) = (τ * z.im) * N := by ring
        _ ≤ 1 * N := by
          have : τ * z.im ≤ 1 := by
            calc τ * z.im ≤ τ * τ⁻¹ := mul_le_mul_of_nonneg_left hηT hτ.le
              _ = 1 := mul_inv_cancel₀ hτ.ne'
          exact mul_le_mul_of_nonneg_right this hN0.le
        _ = 1 * N := rfl
    have hXlow : (τ / N) ^ (2 * p) ≤ Xp := by
      rw [hXp, pow_mul]
      calc ((τ / N) ^ 2) ^ p ≤ (Ψ ^ 2) ^ p :=
            pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hΨτ 2) p
        _ ≤ ((N : ℝ) ^ δ * Ψ ^ 2) ^ p := by
            refine pow_le_pow_left₀ (by positivity) ?_ p
            exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow hNr hδ.le)
    have hDa' : (4 + 7 * p : ℝ) ≤ Da := by
      refine le_trans ?_ hDa
      unfold dPrev
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      nlinarith
    have hpow : (N : ℝ) ^ (4 + 7 * p) * (N : ℝ) ^ (-Da) ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hNr (by push_cast; linarith)
    have hτN : (τ / N) ^ (2 * p) = τ ^ (2 * p) * ((N : ℝ) ^ (2 * p))⁻¹ := by
      rw [div_pow]; ring
    calc Cd * (N : ℝ) ^ (2 + 5 * p) * (ℙ Ξᶜ).toReal
        ≤ Cd * (N : ℝ) ^ (2 + 5 * p) * ((9 * (N : ℝ)) ^ 2 * (N : ℝ) ^ (-Da)) :=
          mul_le_mul_of_nonneg_left hPr (by positivity)
      _ = 81 * Cd * ((N : ℝ) ^ (4 + 7 * p) * (N : ℝ) ^ (-Da)) * ((N : ℝ) ^ (2 * p))⁻¹ := by
          rw [show 4 + 7 * p = (2 + 5 * p) + 2 + 2 * p by ring, pow_add, pow_add]
          field_simp
          ring
      _ ≤ 81 * Cd * 1 * ((N : ℝ) ^ (2 * p))⁻¹ := by gcongr
      _ = 81 * Cd * τ⁻¹ ^ (2 * p) * (τ / N) ^ (2 * p) := by
          rw [hτN, inv_pow]
          field_simp
      _ ≤ 81 * Cd * τ⁻¹ ^ (2 * p) * Xp := by gcongr
  -- conclusion
  calc (N : ℝ) ^ (-(n : ℝ) / 2) *
        ‖∫ ω, ∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n‖
      ≤ (N : ℝ) ^ (-(n : ℝ) / 2) *
        ∫ ω, ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (Real.rpow_nonneg hN0.le _)
    _ = ∫ ω, (N : ℝ) ^ (-(n : ℝ) / 2) *
        ‖∑ α : UpperIdx N, s α * fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) n‖ :=
        (integral_const_mul _ _).symm
    _ ≤ K₁ * (Xp + bp + EF) + Cd * (N : ℝ) ^ (2 + 5 * p) * (ℙ Ξᶜ).toReal := hsplit
    _ ≤ K₁ * (Xp + bp + EF) + 81 * Cd * τ⁻¹ ^ (2 * p) * Xp := by linarith
    _ ≤ (K₁ + 81 * Cd * τ⁻¹ ^ (2 * p)) * (Xp + bp + EF) := by
        have : 0 ≤ 81 * Cd * τ⁻¹ ^ (2 * p) := by positivity
        nlinarith


#print axioms FtW
#print axioms avgCoeffW
#print axioms wig_avg_coeff

end Anisotropic
