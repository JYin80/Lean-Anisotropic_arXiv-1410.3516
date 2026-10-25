import Anisotropic.Averaged.Main
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.AvgWords
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.Main
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.SelfConsistentII

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Theorem 12.2 (ii): the averaged law for `W + A`, with control `Φ` -/

/-! ## Resolvents of real symmetric matrices -/

section Resolvent

variable {N : ℕ}

/-- `∑_c |y_c|²` for a complex vector `y`. -/
private def avmNsq (y : Fin N → ℂ) : ℝ := ∑ c, ‖y c‖ ^ 2

private lemma avmNsq_nonneg (y : Fin N → ℂ) : 0 ≤ avmNsq y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For a real symmetric `H`, `∑_a conj((H y)_a) y_a` is real. -/
private lemma avm_im_quad {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) (y : Fin N → ℂ) :
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
private lemma avm_ward_of_eq {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ}
    {y v : Fin N → ℂ} (hv : (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ y = v) :
    (∑ a, starRingEnd ℂ (v a) * y a).im = w.im * avmNsq y := by
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
  rw [e, Complex.sub_im, avm_im_quad hH y, ← Complex.ofReal_sum]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_add, avmNsq]
  ring

/-- `H − w` is invertible for `H` real symmetric and `Im w > 0`. -/
private lemma avm_isUnit_det {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ}
    (hw : 0 < w.im) : IsUnit (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h := avm_ward_of_eq hH hMy
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, Complex.zero_im] at h
  have hn : avmNsq y = 0 := by
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
private lemma avm_mul_inv {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ}
    (hw : 0 < w.im) :
    (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (avm_isUnit_det hH hw)

/-- `(H − w)⁻¹` is symmetric for `H` real symmetric. -/
private lemma avm_inv_transpose {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) (w : ℂ) :
    ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᵀ =
      (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  congr 1
  rw [cplx, ← Matrix.transpose_map, hH]

/-- Ward identity: `Im ⟨v, (H − w)⁻¹ v⟩ = Im w · |(H − w)⁻¹ v|²`. -/
private lemma avm_ward {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ} (hw : 0 < w.im)
    (v : Fin N → ℂ) :
    (∑ a, starRingEnd ℂ (v a) *
        ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v) a).im =
      w.im * avmNsq ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v) := by
  refine avm_ward_of_eq hH ?_
  rw [Matrix.mulVec_mulVec, avm_mul_inv hH hw, Matrix.one_mulVec]

/-- `|(H − w)⁻¹ v|² ≤ (Im w)⁻² |v|²`. -/
private lemma avm_opNorm {H : Matrix (Fin N) (Fin N) ℝ} (hH : Hᵀ = H) {w : ℂ} (hw : 0 < w.im)
    (v : Fin N → ℂ) :
    w.im ^ 2 * avmNsq ((cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v) ≤ avmNsq v := by
  set y := (cplx H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v with hy
  have hW := avm_ward hH hw v
  rw [← hy] at hW
  have h1 : w.im * avmNsq y ≤ ∑ a, ‖v a‖ * ‖y a‖ := by
    rw [← hW]
    refine (Complex.im_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : (∑ a, ‖v a‖ * ‖y a‖) ^ 2 ≤ avmNsq v * avmNsq y :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h0 : 0 ≤ w.im * avmNsq y := mul_nonneg hw.le (avmNsq_nonneg y)
  have h3 : (w.im * avmNsq y) ^ 2 ≤ avmNsq v * avmNsq y :=
    (pow_le_pow_left₀ h0 h1 2).trans h2
  have hy0 := avmNsq_nonneg y
  rcases hy0.lt_or_eq with hpos | hzero
  · have : w.im ^ 2 * avmNsq y * avmNsq y ≤ avmNsq v * avmNsq y := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero, mul_zero]
    exact avmNsq_nonneg v

end Resolvent

/-! ## `G^W` and `Π^W` -/

section GPi

variable {N : ℕ}

private lemma avm_symm_of_herm {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  have h := hA.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at h

private lemma avm_symm_add {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) : (Wm + A)ᵀ = Wm + A := by
  rw [Matrix.transpose_add, hW, avm_symm_of_herm hA]

private lemma avm_GW_eq (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    GW A Wm z = (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl

private lemma avm_piW_eq (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    piW A z = (cplx A - (mW (specOf A) z + z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl

/-- `G` is symmetric. -/
private lemma avm_GW_symm {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    (z : ℂ) (a b : Fin N) : GW A Wm z b a = GW A Wm z a b := by
  have h := avm_inv_transpose (avm_symm_add hA hW) z
  rw [← avm_GW_eq] at h
  have := congrFun (congrFun h a) b
  rwa [Matrix.transpose_apply] at this

/-- `testBilin x M x` as a sesquilinear sum. -/
private lemma avm_testBilin_eq (x : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    testBilin x M x = ∑ a, starRingEnd ℂ (cvec x a) * (M *ᵥ cvec x) a := by
  simp [testBilin, dotProduct, cvec, Complex.conj_ofReal]

/-- Ward identity for `G`: `Im ⟨x, G x⟩ = η |G x|²`. -/
private lemma avm_GW_ward {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    {z : ℂ} (hz : 0 < z.im) (x : Fin N → ℝ) :
    (testBilin x (GW A Wm z) x).im = z.im * avmNsq (GW A Wm z *ᵥ cvec x) := by
  rw [avm_testBilin_eq, avm_GW_eq]
  exact avm_ward (avm_symm_add hA hW) hz _

/-- `|G v|² ≤ η⁻² |v|²`. -/
private lemma avm_GW_op {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℂ) :
    z.im ^ 2 * avmNsq (GW A Wm z *ᵥ v) ≤ avmNsq v := by
  rw [avm_GW_eq]
  exact avm_opNorm (avm_symm_add hA hW) hz v

private lemma avm_im_w_pos {A : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) {z : ℂ} (hz : 0 < z.im) :
    0 < (mW (specOf A) z + z).im := by
  have := (mW_spec hN (specOf A) hz).1
  simp only [Complex.add_im]
  linarith

/-- Ward identity for `Π`: `Im ⟨x, Π x⟩ = (Im m + η) |Π x|²`. -/
private lemma avm_piW_ward {A : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (x : Fin N → ℝ) :
    (testBilin x (piW A z) x).im =
      (mW (specOf A) z + z).im * avmNsq (piW A z *ᵥ cvec x) := by
  rw [avm_testBilin_eq, avm_piW_eq]
  exact avm_ward (avm_symm_of_herm hA) (avm_im_w_pos hN hz) _

private lemma avm_testNorm_sq (x : Fin N → ℝ) : testNorm x ^ 2 = ∑ c, x c ^ 2 := by
  rw [testNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- From a bilinear bound `|⟨v, M x⟩| ≤ T |v| |x|` on real vectors: `|M x|² ≤ 2 T² |x|²`. -/
private lemma avm_nsq_le_of_bilin {M : Matrix (Fin N) (Fin N) ℂ} {T : ℝ} (x : Fin N → ℝ)
    (hM : ∀ v : Fin N → ℝ, ‖testBilin v M x‖ ≤ T * testNorm v * testNorm x) :
    avmNsq (M *ᵥ cvec x) ≤ 2 * T ^ 2 * testNorm x ^ 2 := by
  set y := M *ᵥ cvec x with hy
  set yR : Fin N → ℝ := fun c => (y c).re
  set yI : Fin N → ℝ := fun c => (y c).im
  have hR : testBilin yR M x = ∑ c, ((y c).re : ℂ) * y c := by
    simp [testBilin, dotProduct, yR, hy]
  have hI : testBilin yI M x = ∑ c, ((y c).im : ℂ) * y c := by
    simp [testBilin, dotProduct, yI, hy]
  have hsum : avmNsq y = (testBilin yR M x).re + (testBilin yI M x).im := by
    rw [hR, hI, Complex.re_sum, Complex.im_sum, avmNsq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hnR : testNorm yR ^ 2 + testNorm yI ^ 2 = avmNsq y := by
    rw [avm_testNorm_sq, avm_testNorm_sq, avmNsq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : avmNsq y ≤ T * testNorm x * (testNorm yR + testNorm yI) := by
    rw [hsum]
    have a1 := (Complex.re_le_norm (testBilin yR M x)).trans (hM yR)
    have a2 := (Complex.im_le_norm (testBilin yI M x)).trans (hM yI)
    nlinarith
  have hx0 : 0 ≤ testNorm x := Real.sqrt_nonneg _
  have hR0 : 0 ≤ testNorm yR := Real.sqrt_nonneg _
  have hI0 : 0 ≤ testNorm yI := Real.sqrt_nonneg _
  have hy0 : 0 ≤ avmNsq y := avmNsq_nonneg y
  have h2 : avmNsq y ^ 2 ≤ (T * testNorm x) ^ 2 * (2 * avmNsq y) := by
    have e := pow_le_pow_left₀ hy0 h1 2
    have : (testNorm yR + testNorm yI) ^ 2 ≤ 2 * avmNsq y := by
      rw [← hnR]; nlinarith [sq_nonneg (testNorm yR - testNorm yI)]
    calc avmNsq y ^ 2 ≤ (T * testNorm x * (testNorm yR + testNorm yI)) ^ 2 := e
      _ = (T * testNorm x) ^ 2 * (testNorm yR + testNorm yI) ^ 2 := by ring
      _ ≤ (T * testNorm x) ^ 2 * (2 * avmNsq y) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
  rcases hy0.lt_or_eq with hpos | hzero
  · have : avmNsq y * avmNsq y ≤ (2 * T ^ 2 * testNorm x ^ 2) * avmNsq y := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

/-- The real orthogonal matrix of eigenvectors of a symmetric `A`. -/
private lemma avm_eig_decomp {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
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
private lemma avm_resolvent_eq {A U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
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
private lemma avm_trace_piW {A : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : (N : ℂ)⁻¹ * trace (piW A z) = mW (specOf A) z := by
  obtain ⟨U, hUU, hUU', hAU⟩ := avm_eig_decomp hA
  have hw := avm_im_w_pos (A := A) hN hz
  have hne : ∀ k, (hA.eigenvalues k : ℂ) - (mW (specOf A) z + z) ≠ 0 := fun k h0 => by
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at this
    linarith
  have hpi : piW A z = (cplx U) * diagonal
      (fun k => ((hA.eigenvalues k : ℂ) - (mW (specOf A) z + z))⁻¹) * (cplx U)ᵀ :=
    avm_resolvent_eq hUU hUU' hAU hne
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

/-- `tr(G (Δ G)^{k+1}) = tr((Δ G)^k Δ G²)`. -/
private lemma avm_trace_eq (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (k : ℕ) :
    trace (G * (deltaW i j * G) ^ (k + 1)) =
      trace ((deltaW i j * G) ^ k * deltaW i j * (G * G)) := by
  rw [pow_succ, show G * ((deltaW i j * G) ^ k * (deltaW i j * G)) =
    (G * ((deltaW i j * G) ^ k * deltaW i j)) * G by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]

private lemma avm_trace_mul (K H : Matrix (Fin N) (Fin N) ℂ) :
    trace (K * H) = ∑ b, ∑ c, K b c * H c b := by
  simp [Matrix.trace, Matrix.mul_apply]

/-- A nonnegative function supported on `{i, j}` sums to at most `f i + f j`. -/
private lemma avm_sum_two (f : Fin N → ℝ) (i j : Fin N) (h0 : ∀ d, 0 ≤ f d)
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

private lemma avm_delta_ne {i j a b : Fin N} (h : deltaW i j a b ≠ 0) :
    (a = i ∨ a = j) ∧ (b = i ∨ b = j) := by
  simp only [deltaW] at h
  split_ifs at h with h1
  · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h1, Or.inl h2⟩
  · exact absurd rfl h

private lemma avm_norm_delta_le (i j a b : Fin N) : ‖deltaW i j a b‖ ≤ 1 := by
  simp only [deltaW]
  split_ifs <;> simp

/-- `K_l = (Δ G)^l Δ` is supported on `{i, j}²`, with entries at most `(4B)^l`. -/
private lemma avm_K_bound {G : Matrix (Fin N) (Fin N) ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a b, ‖G a b‖ ≤ B) (i j : Fin N) (l : ℕ) :
    ∀ a b, (((deltaW i j * G) ^ l * deltaW i j) a b ≠ 0 → (a = i ∨ a = j) ∧ (b = i ∨ b = j)) ∧
      ‖((deltaW i j * G) ^ l * deltaW i j) a b‖ ≤ (4 * B) ^ l := by
  induction l with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_mul]
    exact ⟨avm_delta_ne, by simpa using avm_norm_delta_le i j a b⟩
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
          exact hc (avm_delta_ne h').1
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
        have := avm_sum_two (fun d => ‖G c d * K d b‖) i j (fun d => norm_nonneg _)
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
      have := avm_sum_two (fun c => ‖deltaW i j a c * ∑ d, G c d * K d b‖) i j
        (fun c => norm_nonneg _) (fun c h1 h2 => by
          have : deltaW i j a c = 0 := by
            by_contra h'
            rcases (avm_delta_ne h').2 with h | h
            · exact h1 h
            · exact h2 h
          simp [this])
      refine this.trans ?_
      have e1 : ∀ c, ‖deltaW i j a c * ∑ d, G c d * K d b‖ ≤ 2 * (B * (4 * B) ^ l) := fun c => by
        rw [norm_mul]
        calc ‖deltaW i j a c‖ * ‖∑ d, G c d * K d b‖ ≤ 1 * (2 * (B * (4 * B) ^ l)) :=
              mul_le_mul (avm_norm_delta_le i j a c) (hin c) (norm_nonneg _) zero_le_one
          _ = 2 * (B * (4 * B) ^ l) := one_mul _
      calc _ ≤ 2 * (B * (4 * B) ^ l) + 2 * (B * (4 * B) ^ l) := add_le_add (e1 i) (e1 j)
        _ = (4 * B) ^ (l + 1) := by ring

/-- `|tr(G (ΔG)^{k+1})| ≤ 4 (4B)^k h` when `|G_{ab}| ≤ B` and `|(G²)_{ab}| ≤ h`. -/
private lemma avm_trace_le {G : Matrix (Fin N) (Fin N) ℂ} {B h : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a b, ‖G a b‖ ≤ B) (hh : ∀ a b, ‖(G * G) a b‖ ≤ h) (i j : Fin N) (k : ℕ) :
    ‖trace (G * (deltaW i j * G) ^ (k + 1))‖ ≤ 4 * (4 * B) ^ k * h := by
  rw [avm_trace_eq, avm_trace_mul]
  set K := (deltaW i j * G) ^ k * deltaW i j with hK
  have hKb := avm_K_bound hB0 hB i j k
  have hh0 : 0 ≤ h := (norm_nonneg _).trans (hh i i)
  have hrow : ∀ b, ‖∑ c, K b c * (G * G) c b‖ ≤ 2 * ((4 * B) ^ k * h) := by
    intro b
    refine (norm_sum_le _ _).trans ?_
    have := avm_sum_two (fun c => ‖K b c * (G * G) c b‖) i j (fun c => norm_nonneg _)
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
  have := avm_sum_two (fun b => ‖∑ c, K b c * (G * G) c b‖) i j (fun b => norm_nonneg _)
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
private lemma avm_avgCoeff_le {A Wm : Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {B h : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hh : ∀ a b, ‖(GW A Wm z * GW A Wm z) a b‖ ≤ h)
    (i j : Fin N) (k : ℕ) :
    ‖avgCoeffW A Wm z i j (k + 1)‖ ≤ 4 * (4 * B) ^ k * h / N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold avgCoeffW
  simp only [Nat.add_one_ne_zero, ite_false, sub_zero, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_inv, Complex.norm_natCast]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (avm_trace_le hB0 hB hh i j k) (inv_nonneg.2 hN)

private lemma avm_avgCoeff_zero (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N) :
    avgCoeffW A Wm z i j 0 = mNW A Wm z - mW (specOf A) z := by
  simp [avgCoeffW, mNW]

end Coeff

/-! ## Sums and coefficient bounds -/

section Sums

variable {N : ℕ}

private lemma avm_le_of_sq {S M : ℝ} (hM : 0 ≤ M) (h : S ^ 2 ≤ M ^ 2) : S ≤ M :=
  (abs_le_of_sq_le_sq' h hM).2

/-- Cauchy–Schwarz for a sum of products of norms, bounded through the two squared sums. -/
private lemma avm_cs {ι : Type*} [Fintype ι] (f g : ι → ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hf : ∑ i, f i ^ 2 ≤ X ^ 2) (hg : ∑ i, g i ^ 2 ≤ Y ^ 2) : ∑ i, f i * g i ≤ X * Y := by
  refine avm_le_of_sq (mul_nonneg hX hY) ?_
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ f g).trans ?_
  rw [mul_pow]
  exact mul_le_mul hf hg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

private lemma avm_card_tuple (p n : ℕ) :
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

/-- `|f_n| ≤ (n+1)^p λ^n (x^p + y^p)` when `|a_0| ≤ x` and `|a_k| ≤ λ^k y` for `1 ≤ k ≤ n`. -/
private lemma avm_fCoeff_le (p n : ℕ) (a : ℕ → ℂ) {x y lam : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
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
    _ ≤ _ := mul_le_mul_of_nonneg_right (avm_card_tuple p n)
        (mul_nonneg (pow_nonneg hl _) (add_nonneg (pow_nonneg hx _) (pow_nonneg hy _)))

private lemma avm_col_eq (M : Matrix (Fin N) (Fin N) ℂ) (a : Fin N) :
    M *ᵥ cvec (Pi.single a (1 : ℝ)) = fun c => M c a := by
  funext c
  simp [Matrix.mulVec, dotProduct, cvec, Pi.single_apply, apply_ite (fun x : ℝ => (x : ℂ)),
    mul_ite]

private lemma avm_testNorm_single (a : Fin N) : testNorm (Pi.single a (1 : ℝ)) = 1 := by
  rw [testNorm]
  have : ∑ c, (Pi.single a (1 : ℝ) : Fin N → ℝ) c ^ 2 = 1 := by
    simp [Pi.single_apply]
  rw [this, Real.sqrt_one]

private lemma avm_testBilin_single (M : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    testBilin (Pi.single a (1 : ℝ)) M (Pi.single b (1 : ℝ)) = M a b := by
  simp [testBilin, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (fun x : ℝ => (x : ℂ)),
    mul_ite, ite_mul]

private lemma avm_testBilin_sub (M M' : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℝ) :
    testBilin v (M - M') w = testBilin v M w - testBilin v M' w := by
  simp [testBilin, Matrix.sub_mulVec, dotProduct_sub]

private lemma avm_nsq_single (a : Fin N) : avmNsq (cvec (Pi.single a (1 : ℝ))) = 1 := by
  simp [avmNsq, cvec, Pi.single_apply]

/-- `|G_{ab}| ≤ |G e_b|`. -/
private lemma avm_entry_le_col (M : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) :
    ‖M a b‖ ^ 2 ≤ avmNsq (fun c => M c b) :=
  Finset.single_le_sum (f := fun c => ‖M c b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- Deterministic bounds: `|G e_a|² ≤ η⁻²`, `|G_{ab}| ≤ η⁻¹`, `|(G²)_{ab}| ≤ η⁻²`. -/
private lemma avm_det_col {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hW : Wmᵀ = Wm)
    {z : ℂ} (hz : 0 < z.im) (a : Fin N) :
    avmNsq (fun c => GW A Wm z c a) ≤ (z.im⁻¹) ^ 2 := by
  have h := avm_GW_op hA hW hz (cvec (Pi.single a (1 : ℝ)))
  rw [avm_col_eq, avm_nsq_single] at h
  rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos hz 2)]
  linarith

/-- `|(G²)_{ab}| ≤ L²` when `G` is symmetric with columns bounded by `L`. -/
private lemma avm_H_le_of_col {G : Matrix (Fin N) (Fin N) ℂ} (hG : ∀ a b, G b a = G a b) {L : ℝ}
    (hL : 0 ≤ L) (hc : ∀ a, avmNsq (fun c => G c a) ≤ L ^ 2) (a b : Fin N) :
    ‖(G * G) a b‖ ≤ L ^ 2 := by
  have e : (G * G) a b = ∑ c, G c a * G c b := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [hG c a]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  have := avm_cs (fun c => ‖G c a‖) (fun c => ‖G c b‖) hL hL (hc a) (hc b)
  simpa [sq] using this

private lemma avm_entry_le {G : Matrix (Fin N) (Fin N) ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ a, avmNsq (fun c => G c a) ≤ L ^ 2) (a b : Fin N) : ‖G a b‖ ≤ L :=
  avm_le_of_sq hL ((avm_entry_le_col G a b).trans (hc b))

private lemma avm_norm_mNW_le {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) {z : ℂ} {L : ℝ}
    (hL : ∀ a, ‖GW A Wm z a a‖ ≤ L) : ‖mNW A Wm z‖ ≤ L := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold mNW
  rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
  calc (N : ℝ)⁻¹ * ‖∑ a, Matrix.diag (GW A Wm z) a‖ ≤ (N : ℝ)⁻¹ * ∑ _a : Fin N, L :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hL a))
          (inv_nonneg.2 hNr.le)
    _ = L := by simp; field_simp

/-- Deterministic bounds on the coefficients: `|a_0| ≤ η⁻¹ + 1`, `|a_{k+1}| ≤ (4η⁻¹)^{k+1} η⁻¹`. -/
private lemma avm_det_coeff {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    ‖avgCoeffW A Wm z i j 0‖ ≤ z.im⁻¹ + 1 ∧
      ∀ k, 1 ≤ k → ‖avgCoeffW A Wm z i j k‖ ≤ (4 * z.im⁻¹) ^ k * z.im⁻¹ := by
  have hη : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  have hcol := avm_det_col hA hW hz (Wm := Wm)
  have hent := avm_entry_le hη hcol
  have hH := avm_H_le_of_col (avm_GW_symm hA hW z) hη hcol
  constructor
  · rw [avm_avgCoeff_zero]
    refine (norm_sub_le _ _).trans (add_le_add (avm_norm_mNW_le hN fun a => hent a a) ?_)
    exact (norm_mW_lt_one hN _ hz).le
  · intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (avm_avgCoeff_le hη hent hH i j k').trans ?_
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h0 : 0 ≤ 4 * (4 * z.im⁻¹) ^ k' * z.im⁻¹ ^ 2 := by positivity
    calc 4 * (4 * z.im⁻¹) ^ k' * z.im⁻¹ ^ 2 / N ≤ 4 * (4 * z.im⁻¹) ^ k' * z.im⁻¹ ^ 2 :=
          div_le_self h0 hNr
      _ = (4 * z.im⁻¹) ^ (k' + 1) * z.im⁻¹ := by ring

private lemma avm_det_fCoeff {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (p n : ℕ) :
    ‖fCoeff p (avgCoeffW A Wm z i j) n‖ ≤
      ((n : ℝ) + 1) ^ p * ((4 * z.im⁻¹) ^ n * ((z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p)) := by
  have hη : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  obtain ⟨h0, hk⟩ := avm_det_coeff hN hA hW hz i j (Wm := Wm)
  exact avm_fCoeff_le p n _ (by positivity) hη (by positivity) h0 fun k hk1 _ => hk k hk1

private lemma avm_FtW_le {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) : FtW A Wm z ≤ z.im⁻¹ + 1 := by
  have := (avm_det_coeff hN hA hW hz (Wm := Wm) ⟨0, by omega⟩ ⟨0, by omega⟩).1
  rwa [avm_avgCoeff_zero] at this

/-- Facts on `Ψ^W`: `(Nη)⁻¹ ≤ Ψ`, `Im m/(Nη) ≤ Ψ²`, and `Ψ ≤ 2` when `Nη ≥ 1`. -/
private lemma avm_psi {a : Fin N → ℝ} (hN : 1 ≤ N) {z : ℂ} (hz : 0 < z.im) :
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
private lemma avm_col_event {A Wm : Matrix (Fin N) (Fin N) ℝ} (hN : 1 ≤ N) (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {τ : ℝ} (hτ : 0 < τ) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hzS : z ∈ S) (hz : 0 < z.im) {κ e : ℝ} (hκ : 0 < κ)
    (hIm : κ * z.im ≤ (mW (specOf A) z).im) (he : 1 ≤ e) (v : Fin N → ℝ)
    (hv : ‖testBilin v (GW A Wm z - piW A z) v‖ ≤ e * PsiW (specOf A) z * testNorm v ^ 2) :
    avmNsq (GW A Wm z *ᵥ cvec v) ≤
      (2 * τ⁻¹ ^ 2 * (1 + κ⁻¹) + 1) * e * N * PsiW (specOf A) z ^ 2 * testNorm v ^ 2 := by
  obtain ⟨hp1, hp2, -⟩ := avm_psi (a := specOf A) hN hz
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
  have hPn : avmNsq (piW A z *ᵥ cvec v) ≤ 2 * τ⁻¹ ^ 2 * testNorm v ^ 2 :=
    avm_nsq_le_of_bilin v fun w => norm_piW_le hτ hA hS hzS w v
  have hW1 := avm_GW_ward hA hW hz v (Wm := Wm)
  have hP1 := avm_piW_ward hN hA hz v
  have hsplit : (testBilin v (GW A Wm z) v).im =
      (testBilin v (piW A z) v).im + (testBilin v (GW A Wm z - piW A z) v).im := by
    rw [avm_testBilin_sub]; simp
  have hD := (Complex.im_le_norm _).trans hv
  have hwim : (m + z).im = m.im + η := by simp [hη]
  rw [hwim] at hP1
  have hG0 := avmNsq_nonneg (GW A Wm z *ᵥ cvec v)
  have hP0 := avmNsq_nonneg (piW A z *ᵥ cvec v)
  -- `η |Gv|² ≤ (Im m + η) 2T² |v|² + e Ψ |v|²`
  have key : η * avmNsq (GW A Wm z *ᵥ cvec v) ≤
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

end Sums

section Meas

variable {N : ℕ}

end Meas

/-! ## Splitting the expectation along the event -/

section Split

/-- If `0 ≤ Z ≤ g` on `Ξ` and `Z ≤ M` everywhere, then `E Z ≤ E g + M P(Ξᶜ)`. -/
private lemma avm_split_int {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
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
private lemma avm_prob {Ω : Type} [MeasureSpace Ω] {N : ℕ} {ι : Type} [Fintype ι]
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
/-! ## Updates of a symmetric matrix -/

/-- The update of a symmetric matrix is symmetric. -/
private lemma avm_Wupd_symm {N : ℕ} {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
    (i j : Fin N) (t : ℝ) : (Wupd Wm i j t)ᵀ = Wupd Wm i j t := by
  ext s u
  simp only [Matrix.transpose_apply, Wupd]
  by_cases h : (u = i ∧ s = j) ∨ (u = j ∧ s = i)
  · have h' : (s = i ∧ u = j) ∨ (s = j ∧ u = i) := by tauto
    simp [h, h']
  · have h' : ¬((s = i ∧ u = j) ∨ (s = j ∧ u = i)) := by tauto
    simp only [h, h', ite_false]
    exact congrFun (congrFun hW s) u

/-- `W^{(ij), W_{ij}} = W` for a symmetric `W`. -/
private lemma avm_Wupd_self {N : ℕ} {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
    (i j : Fin N) : Wupd Wm i j (Wm i j) = Wm := by
  ext s u
  simp only [Wupd]
  by_cases h1 : s = i ∧ u = j
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : s = j ∧ u = i
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [and_self, or_true, ite_true]
      exact (congrFun (congrFun hW s) u)
    · simp [h1, h2]

/-- `W^{(ij), t} + A` is real symmetric. -/
private lemma avm_herm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) (i j : Fin N) (t : ℝ) : (Wupd Wm i j t + A)ᵀ = Wupd Wm i j t + A :=
  avm_symm_add hA (avm_Wupd_symm hW i j t)

/-- `H(y) − H(x) = (y − x) Δ` for `H(t) = W^{(ij),t} + A − z`. -/
private lemma avm_H_sub {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N)
    (x y : ℝ) :
    (cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) -
      (cplx (Wupd Wm i j x + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) =
      ((y - x : ℝ) : ℂ) • deltaW i j := by
  ext s u
  simp only [Matrix.sub_apply, Matrix.smul_apply, cplx, Matrix.map_apply, Matrix.add_apply,
    Wupd, deltaW, smul_eq_mul]
  split_ifs <;> simp

/-- The resolvent identity along the entry `(i, j)`:
`G(y) − G(x) = −(y − x) G(x) Δ G(y)`. -/
private lemma avm_res_id {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x y : ℝ) :
    GW A (Wupd Wm i j y) z - GW A (Wupd Wm i j x) z =
      (-((y - x : ℝ) : ℂ)) • (GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j y) z) := by
  set Hx := cplx (Wupd Wm i j x + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hHx
  set Hy := cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hHy
  have hx : IsUnit Hx.det := avm_isUnit_det (avm_herm hA hW i j x) hz
  have hy : IsUnit Hy.det := avm_isUnit_det (avm_herm hA hW i j y) hz
  have e1 : Hx⁻¹ * Hx = 1 := Matrix.nonsing_inv_mul _ hx
  have e2 : Hy * Hy⁻¹ = 1 := Matrix.mul_nonsing_inv _ hy
  have hs := avm_H_sub A Wm z i j x y
  change Hy⁻¹ - Hx⁻¹ = (-((y - x : ℝ) : ℂ)) • (Hx⁻¹ * deltaW i j * Hy⁻¹)
  have key : Hx⁻¹ * (Hx - Hy) * Hy⁻¹ = Hy⁻¹ - Hx⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [← key, show Hx - Hy = -(Hy - Hx) by abel, hs, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, neg_smul]

/-! ## Derivatives along the entry `(i, j)` -/

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def AvmMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private lemma avm_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : AvmMD f f' x) (hg : AvmMD g g' x) :
    AvmMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private lemma avm_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    AvmMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

/-- `y ↦ G(W^{(ij),y})` is continuous. -/
private lemma avm_continuousAt_G {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) :
    ContinuousAt (fun y => GW A (Wupd Wm i j y) z) x := by
  have hX : Continuous fun y : ℝ =>
      cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    refine Continuous.sub (continuous_matrix fun a b => ?_) continuous_const
    by_cases h : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
    · simp only [cplx, Matrix.map_apply, Matrix.add_apply, Wupd, h, ite_true]
      exact (Complex.continuous_ofReal.comp (continuous_id.add continuous_const))
    · simp only [cplx, Matrix.map_apply, Matrix.add_apply, Wupd, h, ite_false]
      exact continuous_const
  have hu := avm_isUnit_det (avm_herm hA hW i j x) hz
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  exact hinv.comp (f := fun y => cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))
    hX.continuousAt

/-- `d/dy G(W^{(ij),y}) = −G Δ G`. -/
private lemma avm_MD_G {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) :
    AvmMD (fun y => GW A (Wupd Wm i j y) z)
      (-(GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j x) z)) x := by
  intro s t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set G0 := GW A (Wupd Wm i j x) z with hG0
  have hid : ∀ h : ℝ, GW A (Wupd Wm i j (x + h)) z - G0 =
      (-(h : ℂ)) • (G0 * deltaW i j * GW A (Wupd Wm i j (x + h)) z) := by
    intro h
    have e := avm_res_id hA hW hz i j x (x + h)
    rw [show x + h - x = h by ring] at e
    exact e
  have hc : ∀ r, ContinuousAt (fun h : ℝ => GW A (Wupd Wm i j (x + h)) z r t) 0 := fun r => by
    have h2 : ContinuousAt (fun h : ℝ => x + h) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have h3 : ContinuousAt ((fun y => GW A (Wupd Wm i j y) z) ∘ fun h : ℝ => x + h) 0 :=
      ContinuousAt.comp_of_eq (avm_continuousAt_G hA hW hz i j x) h2 (by simp)
    exact ((continuous_apply t).comp (continuous_apply r)).continuousAt.comp h3
  have hE : ContinuousAt
      (fun h : ℝ => (G0 * deltaW i j * GW A (Wupd Wm i j (x + h)) z) s t) 0 := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun r _ => continuousAt_const.mul (hc r)
  have hlim := hE.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [add_zero] at hlim
  refine hlim.neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h : ℂ) ≠ 0 := by simpa using hh
  have := congrFun (congrFun (hid h) s) t
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this, Complex.real_smul]
  push_cast
  field_simp

/-- `d/dy (Δ G)^k = −k (Δ G)^{k+1}`. -/
private lemma avm_MD_pow {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    AvmMD (fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-(k : ℂ) • (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using avm_MD_const (1 : Matrix (Fin N) (Fin N) ℂ) x
  | succ k ih =>
    have hDG := avm_MD_mul (avm_MD_const (deltaW i j) x) (avm_MD_G hA hW hz i j x)
    have h := avm_MD_mul ih hDG
    have e : (fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ (k + 1)) =
        fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ k *
          (deltaW i j * GW A (Wupd Wm i j y) z) :=
      funext fun y => pow_succ _ _
    rw [e]
    convert h using 1
    have e2 : deltaW i j * -(GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j x) z) =
        -((deltaW i j * GW A (Wupd Wm i j x) z) * (deltaW i j * GW A (Wupd Wm i j x) z)) := by
      simp [Matrix.mul_assoc]
    rw [Matrix.zero_mul, zero_add, e2, smul_mul_assoc, ← pow_succ, Matrix.mul_neg,
      ← Matrix.mul_assoc, ← pow_succ, ← pow_succ, Nat.cast_succ, neg_add, add_smul, neg_one_smul]

/-- `d/dy G(Δ G)^k = −(k+1) G(Δ G)^{k+1}`. -/
private lemma avm_MD_T {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    AvmMD (fun y => GW A (Wupd Wm i j y) z * (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-((k : ℂ) + 1) • (GW A (Wupd Wm i j x) z *
        (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1))) x := by
  have h := avm_MD_mul (avm_MD_G hA hW hz i j x) (avm_MD_pow hA hW hz i j x k)
  convert h using 1
  rw [Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_assoc (GW A (Wupd Wm i j x) z) (deltaW i j),
    Matrix.mul_assoc (GW A (Wupd Wm i j x) z), ← pow_succ', neg_add, add_smul, neg_one_smul,
    add_comm]

/-- `d/dx a_k(x) = (k + 1) a_{k+1}(x)` along the entry `(i, j)` of a symmetric matrix. -/
private lemma avm_hasDerivAt_avgCoeffW {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N)
    (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => avgCoeffW A (Wupd Wm i j y) z i j k)
      (((k : ℂ) + 1) * avgCoeffW A (Wupd Wm i j x) z i j (k + 1)) x := by
  have hT := avm_MD_T hA hW hz i j x k
  have htr : HasDerivAt (fun y => trace (GW A (Wupd Wm i j y) z *
      (deltaW i j * GW A (Wupd Wm i j y) z) ^ k))
      (trace (-((k : ℂ) + 1) • (GW A (Wupd Wm i j x) z *
        (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1)))) x := by
    simp only [Matrix.trace, Matrix.diag]
    exact HasDerivAt.fun_sum fun s _ => hT s s
  have h := (htr.const_mul ((-1 : ℂ) ^ k * (N : ℂ)⁻¹)).sub_const
    (if k = 0 then mW (specOf A) z else 0)
  refine h.congr_deriv ?_
  simp only [avgCoeffW, Nat.succ_ne_zero, ↓reduceIte, sub_zero, pow_succ, Matrix.trace_smul,
    smul_eq_mul]
  ring

/-! ## Measurability -/

/-- `W ↦ G^W(z)` is measurable. -/
private lemma avm_measurable_G {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z := by
  refine measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun t => ?_
  have hc : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    refine Continuous.sub ?_ continuous_const
    exact Continuous.matrix_map (continuous_id.add continuous_const) Complex.continuous_ofReal
  have hdet : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := hc.matrix_det.measurable
  have hadj : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t :=
    (Matrix.measurable_iff.1 hc.matrix_adjugate.measurable) s t
  have h : (fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t) =
      fun Wm => (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det⁻¹ *
        (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t := by
    funext Wm
    change (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ s t = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  change Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t
  rw [h]
  exact hdet.inv.mul hadj

/-- `W ↦ a_k(W)` is measurable. -/
private lemma avm_measurable_res {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (i j : Fin N) (k : ℕ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => avgCoeffW A Wm z i j k := by
  have hc : Continuous fun X : Matrix (Fin N) (Fin N) ℂ =>
      (-1 : ℂ) ^ k * (N : ℂ)⁻¹ * trace (X * (deltaW i j * X) ^ k) -
        if k = 0 then mW (specOf A) z else 0 :=
    (continuous_const.mul (continuous_id.matrix_mul
      ((continuous_const.matrix_mul continuous_id).pow k)).matrix_trace).sub continuous_const
  exact hc.measurable.comp (avm_measurable_G A z)

/-- `x ↦ f_n(a(x))` is measurable when every `x ↦ a_k(x)` is. -/
private lemma avm_measurable_fCoeff {X : Type*} [MeasurableSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Measurable fun x => a x k) :
    Measurable fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine Finset.measurable_sum _ fun κ _ => Finset.measurable_prod _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.measurable.comp (ha _)

/-- `(W, t) ↦ W^{(ij),t}` is continuous. -/
private lemma avm_continuous_Wupd {N : ℕ} (i j : Fin N) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => Wupd q.1 i j q.2 := by
  refine continuous_pi fun s => continuous_pi fun u => ?_
  simp only [Wupd]
  split_ifs
  · exact continuous_snd
  · exact continuous_fst.matrix_elem s u

/-- `W ↦ f_n(a(W^{(ij),t}))` is measurable. -/
private lemma avm_measurable_fUpd {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (i j : Fin N) (p n : ℕ) (t : ℝ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      fCoeff p (avgCoeffW A (Wupd Wm i j t) z i j) n :=
  avm_measurable_fCoeff p n fun k => (avm_measurable_res A z i j k).comp
    ((avm_continuous_Wupd i j).measurable.comp (measurable_id.prodMk measurable_const))

/-! ## Deterministic bounds on the coefficients -/

/-- The elementary matrix `E_{ab}`. -/
private def avmE {N : ℕ} (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun s u => if s = a ∧ u = b then 1 else 0

private lemma avm_ent_add {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X + Y) x y = ent X x y + ent Y x y := by
  simp [ent, add_mulVec, dotProduct_add]

/-- `⟨x, X E_{ab} Y y⟩ = ⟨x, X e_a⟩ ⟨e_b, Y y⟩`. -/
private lemma avm_ent_single {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N)
    (x y : Fin N → ℝ) : ent (X * avmE a b * Y) x y = ent X x (eI a) * ent Y (eI b) y := by
  have h1 : ∀ s u, (X * avmE a b) s u = if u = b then X s a else 0 := by
    intro s u
    simp only [Matrix.mul_apply, avmE, Matrix.of_apply]
    by_cases hu : u = b
    · subst hu
      simp
    · simp [hu]
  have h2 : X * avmE a b * Y = fun s t => X s a * Y b t := by
    ext s t
    rw [Matrix.mul_apply]
    simp [h1]
  rw [h2]
  have e1 : ent X x (eI a) = ∑ s, (x s : ℂ) * X s a := by
    simp [ent, cvec, dotProduct, mulVec, eI, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ))]
  have e2 : ent Y (eI b) y = ∑ t, Y b t * (y t : ℂ) := by
    simp [ent, cvec, dotProduct, mulVec, eI, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ))]
  rw [e1, e2, Finset.sum_mul_sum]
  simp only [ent, cvec, dotProduct, mulVec]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

private lemma avm_deltaW_ne {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    deltaW i j = avmE i j + avmE j i := by
  ext s u
  simp only [deltaW, avmE, Matrix.add_apply, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all

private lemma avm_deltaW_eq {N : ℕ} (i : Fin N) : deltaW i i = avmE i i := by
  ext s u
  simp [deltaW, avmE]

/-- `|⟨x, X Δ Y y⟩| ≤ |⟨x, X e_i⟩||⟨e_j, Y y⟩| + |⟨x, X e_j⟩||⟨e_i, Y y⟩|`. -/
private lemma avm_ent_delta_le {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (x y : Fin N → ℝ) :
    ‖ent (X * deltaW i j * Y) x y‖ ≤ ‖ent X x (eI i)‖ * ‖ent Y (eI j) y‖ +
      ‖ent X x (eI j)‖ * ‖ent Y (eI i) y‖ := by
  by_cases h : i = j
  · subst h
    rw [avm_deltaW_eq, avm_ent_single, norm_mul]
    exact le_add_of_nonneg_right (by positivity)
  · rw [avm_deltaW_ne h, Matrix.mul_add, Matrix.add_mul, avm_ent_add, avm_ent_single,
      avm_ent_single]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]

/-! ## The entry `W_{ij}`: Markov, independence, moments -/

private lemma avm_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

/-- `|y| ≤ N^{ε − 1/2}` with probability `≥ 1 − N^{−D}`, from the moments of `√N y` (Markov). -/
private lemma avm_markov (C : ℕ → ℝ) (ε D : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (y : Ω → ℝ), (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
        ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q) →
      HighProbAt N D {ω | |y ω| ≤ (N : ℝ) ^ (ε - 1 / 2)} := by
  set q : ℕ := ⌈2 * max D 0 / ε⌉₊ + 1 with hq
  set Cq := max (C q) 1 with hCq
  refine ⟨max 1 ⌈Cq ^ (ε / 2)⁻¹⌉₊, fun N hN Ω _ _ y hy => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hCqN : Cq ≤ (N : ℝ) ^ (ε / 2) :=
    avm_le_rpow (zero_le_one.trans (le_max_right _ _)) (by positivity)
      (le_trans (le_max_right _ _) hN)
  have hq1 : 2 * max D 0 / ε ≤ (q : ℝ) := by
    rw [hq]; push_cast
    linarith [Nat.le_ceil (2 * max D 0 / ε)]
  have hp : D ≤ (ε - ε / 2) * q := by
    calc D ≤ max D 0 := le_max_left _ _
      _ = (ε - ε / 2) * (2 * max D 0 / ε) := by field_simp; ring
      _ ≤ (ε - ε / 2) * q := mul_le_mul_of_nonneg_left hq1 (by linarith)
  have hNe1 : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1r (by positivity)
  have hmom : ∫ ω, |Real.sqrt N * y ω| ^ q ≤ ((N : ℝ) ^ (ε / 2) * 1) ^ q := by
    rw [mul_one]
    calc ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q := (hy q).2
      _ ≤ Cq := le_max_left _ _
      _ ≤ (N : ℝ) ^ (ε / 2) := hCqN
      _ ≤ ((N : ℝ) ^ (ε / 2)) ^ q := le_self_pow₀ hNe1 (by omega)
  have hd := DomAt.of_moment (ε := ε / 2) (ε' := ε) (D := D) (ζ := 1)
    (ξ := fun ω => |Real.sqrt N * y ω|) q hN1 hp (fun ω => abs_nonneg _) one_pos
    (hy q).1 hmom
  unfold DomAt at hd
  unfold HighProbAt
  refine le_trans (measure_mono fun ω hω => ?_) hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
  have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  rw [abs_mul, abs_of_pos hsq0, mul_one]
  have e : (N : ℝ) ^ ε = Real.sqrt N * (N : ℝ) ^ (ε - 1 / 2) := by
    rw [hsq, ← Real.rpow_add hNp]; ring_nf
  rw [e]
  exact mul_lt_mul_of_pos_left hω hsq0

/-- `W_{ij}` is independent of `W^{(ij),0}` (the other upper entries), for `i ≤ j`. -/
private lemma avm_indep {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N) :
    IndepFun (fun ω => Wupd (W ω) α.1.1 α.1.2 0) (fun ω => W ω α.1.1 α.1.2) := by
  set i := α.1.1 with hi
  set j := α.1.2 with hj
  set T : Finset (UpperIdx N) := {α} with hT
  set S : Finset (UpperIdx N) := Finset.univ.erase α with hS
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_singleton_right]
    exact Finset.notMem_erase _ _
  have h := hW.indep.indepFun_finset S T hST (fun q => hW.measurable q.1.1 q.1.2)
  have key : ∀ s u : Fin N, ¬((s = i ∧ u = j) ∨ (s = j ∧ u = i)) →
      (⟨(min s u, max s u), min_le_max⟩ : UpperIdx N) ∈ S := by
    intro s u hc
    rw [hS, Finset.mem_erase]
    refine ⟨fun heq => ?_, Finset.mem_univ _⟩
    have h1 : min s u = i := congrArg (fun q : UpperIdx N => q.1.1) heq
    have h2 : max s u = j := congrArg (fun q : UpperIdx N => q.1.2) heq
    rcases le_total s u with hsu | hus
    · rw [min_eq_left hsu] at h1
      rw [max_eq_right hsu] at h2
      exact hc (Or.inl ⟨h1, h2⟩)
    · rw [min_eq_right hus] at h1
      rw [max_eq_left hus] at h2
      exact hc (Or.inr ⟨h2, h1⟩)
  have hsym : ∀ ω (s u : Fin N), W ω (min s u) (max s u) = W ω s u := by
    intro ω s u
    rcases le_total s u with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact congrFun (congrFun (hW.symm ω) s) u
  let φ : (S → ℝ) → Matrix (Fin N) (Fin N) ℝ := fun x s u =>
    if (s = i ∧ u = j) ∨ (s = j ∧ u = i) then 0 else
      if hm : (⟨(min s u, max s u), min_le_max⟩ : UpperIdx N) ∈ S then x ⟨_, hm⟩ else 0
  let ψ : (T → ℝ) → ℝ := fun x => x ⟨α, Finset.mem_singleton_self _⟩
  have hφ : Measurable φ := by
    refine measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun u => ?_
    simp only [φ]
    split_ifs
    · exact measurable_const
    · exact measurable_pi_apply _
    · exact measurable_const
  have hψ : Measurable ψ := measurable_pi_apply _
  have h2 := h.comp hφ hψ
  have e1 : (φ ∘ fun a (q : S) => W a (q : UpperIdx N).1.1 (q : UpperIdx N).1.2) =
      fun ω => Wupd (W ω) i j 0 := by
    funext ω s u
    simp only [Function.comp, φ, Wupd]
    by_cases hc : (s = i ∧ u = j) ∨ (s = j ∧ u = i)
    · simp [hc]
    · simp only [hc, key s u hc, ↓reduceIte, ↓reduceDIte]
      exact hsym ω s u
  have e2 : (ψ ∘ fun a (q : T) => W a (q : UpperIdx N).1.1 (q : UpperIdx N).1.2) =
      fun ω => W ω i j := rfl
  rw [e1, e2] at h2
  exact h2

/-- `|E W_{ij}^k| ≤ N^{−k/2} max(C_k, 0)`. -/
private lemma avm_moment_entry {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (hN : 1 ≤ N)
    (i j : Fin N) (k : ℕ) :
    ‖∫ ω, (W ω i j : ℂ) ^ k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have e : ∀ x : ℝ, ‖(x : ℂ) ^ k‖ = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * x| ^ k := by
    intro x
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hs, mul_pow,
      ← mul_assoc]
    have : (N : ℝ) ^ (-(k : ℝ) / 2) * Real.sqrt N ^ k = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp,
        show -(k : ℝ) / 2 + 1 / 2 * k = 0 by ring, Real.rpow_zero]
    rw [this, one_mul]
  calc ‖∫ ω, (W ω i j : ℂ) ^ k‖ ≤ ∫ ω, ‖(W ω i j : ℂ) ^ k‖ := norm_integral_le_integral_norm _
    _ = (N : ℝ) ^ (-(k : ℝ) / 2) * ∫ ω, |Real.sqrt N * W ω i j| ^ k := by
        simp_rw [e]; exact integral_const_mul _ _
    _ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 :=
        mul_le_mul_of_nonneg_left ((hW.moment k i j).trans (le_max_left _ _)) (by positivity)

/-! ## Moment functions, product spaces and the laws of single entries -/

/-- `momMaxW` is idempotent. -/
private lemma avm_momMaxW_idem (C : ℕ → ℝ) : momMaxW (momMaxW C) = momMaxW C := by
  funext p
  unfold momMaxW
  rw [max_assoc, max_self]

/-- The Gaussian moment term is bounded by `momMaxW`. -/
private lemma avm_goe_le_momMaxW (C : ℕ → ℝ) (p : ℕ) :
    (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p ≤ momMaxW C p := le_max_right _ _

private lemma avm_momMaxW_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ momMaxW C p := by
  refine le_trans ?_ (avm_goe_le_momMaxW C p)
  have : 0 ≤ gaussMoment p := by
    unfold gaussMoment; exact integral_nonneg fun x => by positivity
  positivity

/-- The interpolants lie in the class with moments `momMaxW C` when `W` does. -/
private lemma avm_class_interp {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries (momMaxW C) N W) {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    WigClassEntries (momMaxW C)
      (Ω := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) N ofUpper := by
  have h := wigClass_interp hN hW h₀ h₁
  rwa [avm_momMaxW_idem] at h

/-- The product space `∏_α ν_α` over the upper-triangular indices. -/
private def AvmPi (N : ℕ) (_ν : UpperIdx N → Measure ℝ) : Type := UpperIdx N → ℝ

private instance (N : ℕ) (ν : UpperIdx N → Measure ℝ) : MeasurableSpace (AvmPi N ν) :=
  MeasurableSpace.pi

private instance (N : ℕ) (ν : UpperIdx N → Measure ℝ) : MeasureSpace (AvmPi N ν) :=
  ⟨Measure.pi ν⟩

private lemma avm_isProb_pi {N : ℕ} (ν : UpperIdx N → Measure ℝ) [∀ α, IsProbabilityMeasure (ν α)] :
    IsProbabilityMeasure (ℙ : Measure (AvmPi N ν)) := by
  change IsProbabilityMeasure (Measure.pi ν)
  infer_instance

/-- The moment, mean and variance conditions of the class for one law on `ℝ`. -/
private structure AvmULaw (N : ℕ) (C : ℕ → ℝ) (lo hi : ℝ) (ν : Measure ℝ) : Prop where
  integrable : ∀ p : ℕ, Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν
  mean : ∫ x, x ∂ν = 0
  var_ge : lo ≤ ∫ x, x ^ 2 ∂ν
  var_le : ∫ x, x ^ 2 ∂ν ≤ hi
  moment : ∀ p : ℕ, ∫ x, |Real.sqrt N * x| ^ p ∂ν ≤ C p

/-- The upper index `(min i j, max i j)` of the entry `(i, j)`. -/
private def avmUp {N : ℕ} (i j : Fin N) : UpperIdx N := ⟨(min i j, max i j), min_le_max⟩

/-- The variance bound of the entry `α`: `2/N` on the diagonal and `1/N` off it. -/
private def avmVarHi (N : ℕ) (α : UpperIdx N) : ℝ := if α.1.1 = α.1.2 then 2 / (N : ℝ) else 1 / N

private lemma avm_goeLaw_prob (N : ℕ) (α : UpperIdx N) : IsProbabilityMeasure (goeLaw N α) := by
  unfold goeLaw
  infer_instance

private lemma avm_entryLawW_prob {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (α : UpperIdx N) : IsProbabilityMeasure (entryLawW W α) :=
  ⟨by simp [entryLawW, Measure.map_apply (hW α.1.1 α.1.2) MeasurableSet.univ]⟩

/-- The entry law `α` of a matrix in the class satisfies `AvmULaw`. -/
private lemma avm_entryLawW_uLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N) :
    AvmULaw N C (1 / N) (avmVarHi N α) (entryLawW W α) := by
  have hm : AEMeasurable (fun ω => W ω α.1.1 α.1.2) (ℙ : Measure Ω) :=
    (hW.measurable _ _).aemeasurable
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∫ x, f x ∂(entryLawW W α) = ∫ ω, f (W ω α.1.1 α.1.2) := fun f hf =>
    integral_map hm hf.aestronglyMeasurable
  refine ⟨fun p => ?_, ?_, ?_, ?_, fun p => ?_⟩
  · exact (integrable_map_measure
      (by fun_prop : Continuous fun x : ℝ => |Real.sqrt N * x| ^ p).aestronglyMeasurable
      hm).2 (hW.integrable_moment p _ _)
  · simpa using (key (fun x => x) continuous_id).trans (hW.mean _ _)
  · rw [key (fun x => x ^ 2) (by fun_prop)]
    by_cases h : α.1.1 = α.1.2
    · rw [h]
      exact hW.var_diag_ge _
    · exact (hW.var_off _ _ h).ge
  · rw [key (fun x => x ^ 2) (by fun_prop)]
    by_cases h : α.1.1 = α.1.2
    · simp only [avmVarHi, h, ite_true]
      exact hW.var_diag_le _
    · simp only [avmVarHi, h, ite_false]
      exact (hW.var_off _ _ h).le
  · exact (key (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le (hW.moment p _ _)

private lemma AvmULaw.mono {N : ℕ} {C C' : ℕ → ℝ} {lo hi : ℝ} {ν : Measure ℝ}
    (h : AvmULaw N C lo hi ν)
    (hC : ∀ p, C p ≤ C' p) : AvmULaw N C' lo hi ν :=
  ⟨h.integrable, h.mean, h.var_ge, h.var_le, fun p => (h.moment p).trans (hC p)⟩

/-- The entry law of the GOE matrix `goeW N` is `goeLaw N`. -/
private lemma avm_entryLawW_goeW (N : ℕ) (α : UpperIdx N) : entryLawW (goeW N) α = goeLaw N α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  change i ≤ j at hij
  simp only [entryLawW, goeLaw]
  rcases hij.lt_or_eq with h | h
  · rw [(isGOE_goeW N).law_off i j h]
    simp [goeVar, h.ne]
  · subst h
    rw [(isGOE_goeW N).law_diag i]
    simp [goeVar]

/-- The GOE entry law satisfies `AvmULaw` with moments `momMaxW C`. -/
private lemma avm_goeLaw_uLaw {N : ℕ} (hN : 1 ≤ N) (C : ℕ → ℝ) (α : UpperIdx N) :
    AvmULaw N (momMaxW C) (1 / N) (avmVarHi N α) (goeLaw N α) := by
  rw [← avm_entryLawW_goeW]
  exact (avm_entryLawW_uLaw ((isGOE_goeW N).classEntries hN) α).mono
    (avm_goe_le_momMaxW C)

/-- Integrability of `|√N x|^p` gives integrability of `x^p`. -/
private lemma avm_integrable_pow_of_sqrt {N : ℕ} (hN : 1 ≤ N) {ν : Measure ℝ} {p : ℕ}
    (h : Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν) :
    Integrable (fun x : ℝ => x ^ p) ν := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine (h.const_mul ((Real.sqrt N)⁻¹ ^ p)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hs.ne', one_pow, one_mul]

private lemma avm_integrable_mix {θ : ℝ} {ρ₀ ρ₁ : Measure ℝ} {f : ℝ → ℝ}
    (hf₀ : Integrable f ρ₀) (hf₁ : Integrable f ρ₁) : Integrable f (mixMeasure θ ρ₀ ρ₁) :=
  (hf₁.smul_measure ENNReal.ofReal_ne_top).add_measure (hf₀.smul_measure ENNReal.ofReal_ne_top)

/-- A mixture of two laws satisfying `AvmULaw` with the same moment function satisfies it. -/
private lemma AvmULaw.mix {N : ℕ} (hN : 1 ≤ N) {C : ℕ → ℝ} {lo hi : ℝ} {ν₀ ν₁ : Measure ℝ}
    (h₀ : AvmULaw N C lo hi ν₀) (h₁ : AvmULaw N C lo hi ν₁) {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : AvmULaw N C lo hi (mixMeasure θ ν₀ ν₁) := by
  have hi : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ p) ν₀ ∧ Integrable (fun x : ℝ => x ^ p) ν₁ :=
    fun p => ⟨avm_integrable_pow_of_sqrt hN (h₀.integrable p),
      avm_integrable_pow_of_sqrt hN (h₁.integrable p)⟩
  have hvar := integral_mixMeasure hθ₀ hθ₁ (hi 2).1 (hi 2).2
  have hc : 0 ≤ 1 - θ := sub_nonneg.2 hθ₁
  refine ⟨fun p => avm_integrable_mix (h₀.integrable p) (h₁.integrable p), ?_, ?_, ?_,
    fun p => ?_⟩
  · have e := integral_mixMeasure hθ₀ hθ₁ (by simpa using (hi 1).1) (by simpa using (hi 1).2)
    rw [e, h₀.mean, h₁.mean]
    ring
  · rw [hvar]
    nlinarith [mul_le_mul_of_nonneg_left h₁.var_ge hθ₀, mul_le_mul_of_nonneg_left h₀.var_ge hc]
  · rw [hvar]
    nlinarith [mul_le_mul_of_nonneg_left h₁.var_le hθ₀, mul_le_mul_of_nonneg_left h₀.var_le hc]
  · rw [integral_mixMeasure hθ₀ hθ₁ (h₀.integrable p) (h₁.integrable p)]
    have a := h₁.moment p
    have b := h₀.moment p
    nlinarith [mul_le_mul_of_nonneg_left a hθ₀, mul_le_mul_of_nonneg_left b hc]

/-- Coordinate integrals under `∏_α ν_α`. -/
private lemma avm_integral_coord {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)]
    (α : UpperIdx N) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (ν α)) :
    ∫ ω : AvmPi N ν, f (ω α) = ∫ x, f x ∂(ν α) :=
  integral_comp_eval (μ := ν) hf

private lemma avm_integrable_coord {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)] (α : UpperIdx N) {f : ℝ → ℝ} (hf : Integrable f (ν α)) :
    Integrable (fun ω : AvmPi N ν => f (ω α)) := integrable_comp_eval (μ := ν) hf

/-- The coordinate matrix under a product of laws satisfying `AvmULaw` lies in the class. -/
private lemma avm_class_pi {C : ℕ → ℝ} {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)] (hν : ∀ α, AvmULaw N C (1 / N) (avmVarHi N α) (ν α)) :
    WigClassEntries C (Ω := AvmPi N ν) N ofUpper := by
  have key : ∀ (i j : Fin N) (f : ℝ → ℝ), Continuous f →
      ∫ ω : AvmPi N ν, f (ofUpper ω i j) = ∫ x, f x ∂(ν (avmUp i j)) :=
    fun i j f hf => avm_integral_coord ν (avmUp i j) hf.aestronglyMeasurable
  refine ⟨fun i j => measurable_pi_apply (X := fun _ : UpperIdx N => ℝ) (avmUp i j),
    fun ω => ?_, ?_, fun i j => ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_,
    fun p i j => ?_, fun p i j => ?_⟩
  · ext i j
    simp [ofUpper, min_comm, max_comm]
  · have h := iIndepFun_pi (μ := ν) (X := fun _ x => x) fun _ => aemeasurable_id
    have e : (fun (p : UpperIdx N) (ω : UpperIdx N → ℝ) => ofUpper ω p.1.1 p.1.2) =
        fun p ω => ω p := by
      funext p ω
      simp [ofUpper, min_eq_left p.2, max_eq_right p.2]
    change iIndepFun (fun (p : UpperIdx N) (ω : UpperIdx N → ℝ) => ofUpper ω p.1.1 p.1.2)
      (Measure.pi ν)
    rw [e]
    exact h
  · exact (key i j (fun x => x) continuous_id).trans (hν (avmUp i j)).mean
  · have hv := hν (avmUp i j)
    have hne : (avmUp i j).1.1 ≠ (avmUp i j).1.2 := fun h =>
      hij (le_antisymm ((le_max_left i j).trans (h.symm.le.trans (min_le_right i j)))
        ((le_max_right i j).trans (h.symm.le.trans (min_le_left i j))))
    have e := key i j (fun x => x ^ 2) (by fun_prop)
    have hle : ∫ x, x ^ 2 ∂(ν (avmUp i j)) ≤ 1 / (N : ℝ) := by
      have := hv.var_le
      simpa only [avmVarHi, hne, ite_false] using this
    exact e.trans (le_antisymm hle hv.var_ge)
  · have e := key i i (fun x => x ^ 2) (by fun_prop)
    exact (hν (avmUp i i)).var_ge.trans_eq e.symm
  · have e := key i i (fun x => x ^ 2) (by fun_prop)
    have hv : avmVarHi N (avmUp i i) = 2 / (N : ℝ) := by simp [avmVarHi, avmUp]
    exact e.trans_le (hv ▸ (hν (avmUp i i)).var_le)
  · exact avm_integrable_coord ν (avmUp i j)
      (f := fun x : ℝ => |Real.sqrt N * x| ^ p) ((hν (avmUp i j)).integrable p)
  · exact (key i j (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le
      ((hν (avmUp i j)).moment p)

/-- The coordinate matrix has vanishing third moments when every coordinate law has. -/
private lemma avm_zeroThird_pi {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)]
    (h3 : ∀ α, ∫ x, x ^ 3 ∂(ν α) = 0) :
    ∀ i j, ∫ ω : AvmPi N ν, (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) i j ^ 3 = 0 := by
  intro i j
  have e := avm_integral_coord ν (avmUp i j) (f := fun x : ℝ => x ^ 3)
    (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable
  exact e.trans (h3 _)

/-- The third moment of a centred Gaussian vanishes. -/
private lemma avm_integral_cube_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  have h := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ => -x) (f := fun x : ℝ => x ^ 3)
    (by fun_prop) (by fun_prop)
  rw [gaussianReal_map_neg, neg_zero] at h
  have e : ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) := fun x => by ring
  simp_rw [e, integral_neg] at h
  linarith

/-- The pair family: the interpolating laws, with the factor `α` replaced by `ρ`. -/
private def avmPairLaw {N : ℕ} (θ : ℝ) (ρ₀ ρ₁ : UpperIdx N → Measure ℝ) (α : UpperIdx N)
    (ρ : Measure ℝ) : UpperIdx N → Measure ℝ :=
  Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ

private lemma avm_pairLaw_prob {N : ℕ} (θ : ℝ) (ρ₀ ρ₁ : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (β : UpperIdx N) :
    IsProbabilityMeasure (avmPairLaw θ ρ₀ ρ₁ α ρ β) := by
  unfold avmPairLaw
  by_cases h : β = α
  · subst h; simpa using ‹IsProbabilityMeasure ρ›
  · simpa [Function.update_of_ne h] using isProbabilityMeasure_mixMeasure θ (ρ₀ β) (ρ₁ β)

/-- The pair matrices lie in the class with moments `momMaxW C`. -/
private lemma avm_class_pair {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries (momMaxW C) N W) {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : AvmULaw N (momMaxW C) (1 / N) (avmVarHi N α) ρ) :
    haveI : ∀ α, IsProbabilityMeasure (goeLaw N α) := avm_goeLaw_prob N
    haveI : ∀ α, IsProbabilityMeasure (entryLawW W α) := avm_entryLawW_prob hW.measurable
    haveI := avm_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
    WigClassEntries (momMaxW C)
      (Ω := AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α ρ)) N ofUpper := by
  have : ∀ α, IsProbabilityMeasure (goeLaw N α) := avm_goeLaw_prob N
  have : ∀ α, IsProbabilityMeasure (entryLawW W α) := avm_entryLawW_prob hW.measurable
  have := avm_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
  refine avm_class_pi _ fun β => ?_
  unfold avmPairLaw
  by_cases h : β = α
  · subst h
    simpa using hρ
  · rw [Function.update_of_ne h]
    exact (avm_goeLaw_uLaw hN C β).mix hN (avm_entryLawW_uLaw hW β) h₀ h₁

/-- Third moment of the entry law of a matrix with vanishing third moments. -/
private lemma avm_entryLawW_third {Ω : Type*} [MeasureSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (h3 : ∀ i j, ∫ ω, W ω i j ^ 3 = 0) (α : UpperIdx N) : ∫ x, x ^ 3 ∂(entryLawW W α) = 0 :=
  (integral_map (hW α.1.1 α.1.2).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable).trans (h3 _ _)

/-- The pair matrices have vanishing third moments when `W` has. -/
private lemma avm_zeroThird_pair {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (h3 : ∀ i j, ∫ ω, W ω i j ^ 3 = 0) {θ : ℝ} (h₀ : 0 ≤ θ)
    (h₁ : θ ≤ 1) (α : UpperIdx N) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∫ x, x ^ 3 ∂ρ = 0) :
    haveI : ∀ α, IsProbabilityMeasure (goeLaw N α) := avm_goeLaw_prob N
    haveI : ∀ α, IsProbabilityMeasure (entryLawW W α) := avm_entryLawW_prob hW.measurable
    haveI := avm_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
    ∀ i j, ∫ ω : AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α ρ),
      (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) i j ^ 3 = 0 := by
  have : ∀ α, IsProbabilityMeasure (goeLaw N α) := avm_goeLaw_prob N
  have : ∀ α, IsProbabilityMeasure (entryLawW W α) := avm_entryLawW_prob hW.measurable
  have := avm_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
  refine avm_zeroThird_pi _ fun β => ?_
  unfold avmPairLaw
  by_cases h : β = α
  · subst h
    simpa using hρ
  · rw [Function.update_of_ne h]
    have hi₀ := avm_integrable_pow_of_sqrt hN ((avm_goeLaw_uLaw hN C β).integrable 3)
    have hi₁ := avm_integrable_pow_of_sqrt hN ((avm_entryLawW_uLaw hW β).integrable 3)
    rw [integral_mixMeasure h₀ h₁ hi₀ hi₁, avm_entryLawW_third hW.measurable h3 β]
    have : ∫ x, x ^ 3 ∂(goeLaw N β) = 0 := avm_integral_cube_gaussianReal _
    rw [this]
    ring

/-! ## Integrals of invariant functions and endpoint laws -/

/-- A bounded measurable real function not depending on the coordinate `α` has the same
integral under `interpLawAt θ ρ₀ ρ₁ α ρ` and under `interpLaw θ ρ₀ ρ₁`. -/
private lemma avm_integral_inv_real {N : ℕ} {θ : ℝ} {ρ₀ ρ₁ : UpperIdx N → Measure ℝ}
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {h : (UpperIdx N → ℝ) → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, |h x| ≤ B) (hinv : ∀ x t, h (Function.update x α t) = h x) :
    ∫ x, h x ∂(interpLawAt θ ρ₀ ρ₁ α ρ) = ∫ x, h x ∂(interpLaw θ ρ₀ ρ₁) := by
  have := avm_pairLaw_prob θ ρ₀ ρ₁ α ρ
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have : IsProbabilityMeasure (interpLaw θ ρ₀ ρ₁) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure (interpLawAt θ ρ₀ ρ₁ α ρ) := by
    unfold interpLawAt
    change IsProbabilityMeasure (Measure.pi (avmPairLaw θ ρ₀ ρ₁ α ρ))
    infer_instance
  have hint : Integrable h (interpLawAt θ ρ₀ ρ₁ α ρ) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  rw [integral_interpLawAt_eq α ρ hm hint]
  simp_rw [hinv]
  rw [integral_fun_fst]
  simp

/-- The complex version of `avm_integral_inv_real`. -/
private lemma avm_integral_inv {N : ℕ} {θ : ℝ} {ρ₀ ρ₁ : UpperIdx N → Measure ℝ}
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {h : (UpperIdx N → ℝ) → ℂ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (hinv : ∀ x t, h (Function.update x α t) = h x) :
    ∫ x, h x ∂(interpLawAt θ ρ₀ ρ₁ α ρ) = ∫ x, h x ∂(interpLaw θ ρ₀ ρ₁) := by
  have := avm_pairLaw_prob θ ρ₀ ρ₁ α ρ
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have : IsProbabilityMeasure (interpLawAt θ ρ₀ ρ₁ α ρ) := by
    unfold interpLawAt
    change IsProbabilityMeasure (Measure.pi (avmPairLaw θ ρ₀ ρ₁ α ρ))
    infer_instance
  have : IsProbabilityMeasure (interpLaw θ ρ₀ ρ₁) := by
    unfold interpLaw
    infer_instance
  have hi1 : Integrable h (interpLawAt θ ρ₀ ρ₁ α ρ) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hi2 : Integrable h (interpLaw θ ρ₀ ρ₁) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hre := avm_integral_inv_real (θ := θ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) α ρ
    (h := fun x => (h x).re) (Complex.measurable_re.comp hm) (B := B)
    (fun x => (Complex.abs_re_le_norm _).trans (hB x)) (fun x t => by simp only [hinv])
  have him := avm_integral_inv_real (θ := θ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) α ρ
    (h := fun x => (h x).im) (Complex.measurable_im.comp hm) (B := B)
    (fun x => (Complex.abs_im_le_norm _).trans (hB x)) (fun x t => by simp only [hinv])
  have e1 := integral_re hi1
  have e2 := integral_re hi2
  have e3 := integral_im hi1
  have e4 := integral_im hi2
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at e1 e2 e3 e4
  apply Complex.ext
  · rw [← e1, ← e2, hre]
  · rw [← e3, ← e4, him]

private lemma avm_interpLaw_one {N : ℕ} (ρ₀ ρ₁ : UpperIdx N → Measure ℝ) :
    interpLaw 1 ρ₀ ρ₁ = Measure.pi ρ₁ := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

private lemma avm_interpLaw_zero {N : ℕ} (ρ₀ ρ₁ : UpperIdx N → Measure ℝ) :
    interpLaw 0 ρ₀ ρ₁ = Measure.pi ρ₀ := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

/-- The upper-triangular coordinates of a symmetric matrix determine it. -/
private lemma avm_ofUpper_restrict {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : Mᵀ = M) :
    ofUpper (fun β : UpperIdx N => M β.1.1 β.1.2) = M := by
  ext i j
  simp only [ofUpper]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact congrFun (congrFun hM i) j

/-- For a matrix of the class, the law of its upper coordinates is the product of the entry
laws. -/
private lemma avm_integral_pi_entryLaw {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W)
    {F : Matrix (Fin N) (Fin N) ℝ → ℝ} (hFo : Measurable fun x => F (ofUpper x)) :
    ∫ x, F (ofUpper x) ∂(Measure.pi (entryLawW W)) = ∫ ω, F (W ω) := by
  have hg : Measurable fun ω (β : UpperIdx N) => W ω β.1.1 β.1.2 :=
    measurable_pi_iff.2 fun β => hW.measurable β.1.1 β.1.2
  have hlaw : (ℙ : Measure Ω).map (fun ω (β : UpperIdx N) => W ω β.1.1 β.1.2) =
      Measure.pi (entryLawW W) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map
      (fun β : UpperIdx N => (hW.measurable β.1.1 β.1.2).aemeasurable)).1 hW.indep]
    rfl
  rw [← hlaw, integral_map hg.aemeasurable hFo.aestronglyMeasurable]
  congr 1
  funext ω
  rw [avm_ofUpper_restrict (hW.symm ω)]

private lemma avm_measurable_ofUpper {N : ℕ} :
    Measurable (ofUpper : (UpperIdx N → ℝ) → Matrix (Fin N) (Fin N) ℝ) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    measurable_pi_apply (X := fun _ : UpperIdx N => ℝ) (avmUp i j)

private lemma avm_measurable_Ft {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun M : Matrix (Fin N) (Fin N) ℝ => FtW A M z := by
  have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℂ =>
      ‖(N : ℂ)⁻¹ * trace M - mW (specOf A) z‖ :=
    ((continuous_const.mul continuous_id.matrix_trace).sub continuous_const).norm
  exact hc.measurable.comp (avm_measurable_G A z)

private lemma avm_ofUpper_symm {N : ℕ} (x : UpperIdx N → ℝ) :
    (ofUpper x : Matrix (Fin N) (Fin N) ℝ)ᵀ = ofUpper x := by
  ext i j
  simp [ofUpper, min_comm, max_comm]

/-! ## The expansion of one Lindeberg term -/

private lemma avm_up_self {N : ℕ} (α : UpperIdx N) : avmUp α.1.1 α.1.2 = α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  simp only [avmUp]
  congr
  · exact min_eq_left hij
  · exact max_eq_right hij

/-- Updating the coordinate `α` does not change `W^{(α),0}`. -/
private lemma avm_Wupd_ofUpper_update {N : ℕ} (x : UpperIdx N → ℝ) (α : UpperIdx N) (t s : ℝ) :
    Wupd (ofUpper (Function.update x α t)) α.1.1 α.1.2 s =
      Wupd (ofUpper x) α.1.1 α.1.2 s := by
  ext a b
  simp only [Wupd]
  split_ifs with h
  · rfl
  · simp only [ofUpper]
    rw [Function.update_of_ne]
    intro he
    apply h
    have h1 : min a b = α.1.1 := congrArg (fun q : UpperIdx N => q.1.1) he
    have h2 : max a b = α.1.2 := congrArg (fun q : UpperIdx N => q.1.2) he
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at h1
      rw [max_eq_right hab] at h2
      exact Or.inl ⟨h1, h2⟩
    · rw [min_eq_right hab] at h1
      rw [max_eq_left hab] at h2
      exact Or.inr ⟨h2, h1⟩

private lemma avm_fCoeff_zero_eq {N : ℕ} {p : ℕ} (hp : Even p) (A Wm : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (i j : Fin N) :
    fCoeff p (avgCoeffW A Wm z i j) 0 = ((FtW A Wm z ^ p : ℝ) : ℂ) := by
  rw [fCoeff_zero hp, avm_avgCoeff_zero]
  unfold FtW
  push_cast
  rfl

/-- `z.im⁻¹ ≤ N` on `𝐃^W(τ, N)`. -/
private lemma avm_im_inv_le {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {z : ℂ} (hz : z ∈ domW τ N) :
    z.im⁻¹ ≤ N := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  obtain ⟨hη0, -, hηl, -⟩ := hz
  have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ z.im :=
    (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)).trans hηl
  rw [Real.rpow_neg_one] at h1
  exact (inv_le_comm₀ hη0 hNp).2 h1

/-! ## The derivative of `θ ↦ E F_v^p(W^θ)` -/

/-- The moments of a law satisfying `AvmULaw`. -/
private lemma avm_law_mom {N : ℕ} (hN : 1 ≤ N) {C : ℕ → ℝ} {lo hi : ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (h : AvmULaw N C lo hi ν) :
    (∫ y, (y : ℂ) ^ 0 ∂ν = 1) ∧ (∫ y, (y : ℂ) ^ 1 ∂ν = 0) ∧
      (lo = hi → ∫ y, (y : ℂ) ^ 2 ∂ν = lo) ∧
      ∀ k : ℕ, ‖∫ y, (y : ℂ) ^ k ∂ν‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * C k := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simp only [pow_one]
    rw [integral_complex_ofReal, h.mean]
    simp
  · intro hlh
    have e : ∫ y, (y : ℂ) ^ 2 ∂ν = ((∫ y, y ^ 2 ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      push_cast
      rfl
    rw [e, le_antisymm (hlh ▸ h.var_le) h.var_ge]
  · intro k
    have e : ∀ x : ℝ, ‖(x : ℂ) ^ k‖ = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * x| ^ k := by
      intro x
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hs, mul_pow,
        ← mul_assoc]
      have : (N : ℝ) ^ (-(k : ℝ) / 2) * Real.sqrt N ^ k = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp,
          show -(k : ℝ) / 2 + 1 / 2 * k = 0 by ring, Real.rpow_zero]
      rw [this, one_mul]
    calc ‖∫ y, (y : ℂ) ^ k ∂ν‖ ≤ ∫ y, ‖(y : ℂ) ^ k‖ ∂ν := norm_integral_le_integral_norm _
      _ = (N : ℝ) ^ (-(k : ℝ) / 2) * ∫ y, |Real.sqrt N * y| ^ k ∂ν := by
          simp_rw [e]; exact integral_const_mul _ _
      _ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * C k :=
          mul_le_mul_of_nonneg_left (h.moment k) (by positivity)

/-- `τ/N ≤ Ψ^W` on `𝐃^W(τ, N)`. -/
private lemma avm_psi_ge {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (a : Fin N → ℝ) {z : ℂ}
    (hz : z ∈ domW τ N) : τ / N ≤ PsiW a z := by
  obtain ⟨h0, -, -, hη⟩ := hz
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  unfold PsiW
  linarith [Real.sqrt_nonneg ((mW a z).im / (N * z.im))]

private lemma avm_card_upper (N : ℕ) : (Fintype.card (UpperIdx N) : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h := Fintype.card_subtype_le (fun q : Fin N × Fin N => q.1 ≤ q.2)
  rw [Fintype.card_prod, Fintype.card_fin] at h
  have : (Fintype.card (UpperIdx N) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h
  rw [sq]; push_cast at this; exact this

/-- The sum over the diagonal upper indices is the sum over `Fin N`. -/
private lemma avm_sum_diag {N : ℕ} (g : Fin N → ℝ) :
    ∑ α : UpperIdx N, (if α.1.1 = α.1.2 then g α.1.1 else 0) = ∑ i, g i := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun α _ => α.1.1) (fun i _ => ⟨(i, i), le_refl i⟩) ?_ ?_ ?_ ?_ ?_
  · intro α _; exact Finset.mem_univ _
  · intro i _; simp
  · intro α hα
    simp only [Finset.mem_filter] at hα
    obtain ⟨⟨a, b⟩, hab⟩ := α
    simp only at hα
    obtain rfl := hα.2
    rfl
  · intro i _; rfl
  · intro α _; rfl

/-- `N^{−2/2} = N⁻¹`. -/
private lemma avm_rpow_neg_one_half_two {N : ℕ} : (N : ℝ) ^ (-((2 : ℕ) : ℝ) / 2) = (N : ℝ)⁻¹ := by
  rw [show -((2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]

/-! ## The Gaussian start and the moment bound by Grönwall -/

private lemma avm_measurable_goeW (N : ℕ) : Measurable (goeW N) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => (isGOE_goeW N).measurable i j

/-- A moment bound from stochastic domination and a deterministic bound:
`E ξ^p ≤ (N^ε ζ)^p + M^p N^{−D}`. -/
private lemma avm_moment_of_dom {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {ε D ζ M : ℝ} {ξ : Ω → ℝ} (p : ℕ) (hξm : Measurable ξ) (hξ0 : ∀ ω, 0 ≤ ξ ω)
    (hξM : ∀ ω, ξ ω ≤ M) (hζ : 0 ≤ ζ) (hM0 : 0 ≤ M) (hN : 1 ≤ N)
    (h : DomAt N ε D ξ (fun _ => ζ)) :
    ∫ ω, ξ ω ^ p ≤ ((N : ℝ) ^ ε * ζ) ^ p + M ^ p * (N : ℝ) ^ (-D) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  set c : ℝ := (N : ℝ) ^ ε * ζ with hc
  have hc0 : 0 ≤ c := by positivity
  set B : Set Ω := {ω | c < ξ ω} with hB
  have hBm : MeasurableSet B := measurableSet_lt measurable_const hξm
  have hPB : (ℙ : Measure Ω).real B ≤ (N : ℝ) ^ (-D) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hNp.le _)] at this
  have hpt : ∀ ω, ξ ω ^ p ≤ c ^ p + M ^ p * B.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, mul_one]
      have := pow_le_pow_left₀ (hξ0 ω) (hξM ω) p
      have : 0 ≤ c ^ p := pow_nonneg hc0 p
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have : ξ ω ≤ c := not_lt.1 hω
      exact pow_le_pow_left₀ (hξ0 ω) this p
  have hgi : Integrable (fun ω => c ^ p + M ^ p * B.indicator (fun _ => (1 : ℝ)) ω) :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hBm |>.const_mul _)
  have hfi : Integrable (fun ω => ξ ω ^ p) :=
    Integrable.mono' hgi (hξm.pow_const p).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (hξ0 ω) p)]; exact hpt ω)
  calc ∫ ω, ξ ω ^ p ≤ ∫ ω, (c ^ p + M ^ p * B.indicator (fun _ => (1 : ℝ)) ω) :=
        integral_mono hfi hgi hpt
    _ = c ^ p + M ^ p * (ℙ : Measure Ω).real B := by
        rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hBm
          |>.const_mul _), integral_const_mul, integral_indicator hBm]
        simp [Measure.real]
    _ ≤ c ^ p + M ^ p * (N : ℝ) ^ (-D) := by
        gcongr

/-! ## The update of one entry: bounds on `G(W^{(ij),t})` from bounds on `G(W)` -/

section Pert

variable {N : ℕ}

/-- `|(X Δ Y)_{ab}| ≤ |X_{ai}| |Y_{jb}| + |X_{aj}| |Y_{ib}|`. -/
private lemma avm_entry_delta_le (X Y : Matrix (Fin N) (Fin N) ℂ) (i j a b : Fin N) :
    ‖(X * deltaW i j * Y) a b‖ ≤ ‖X a i‖ * ‖Y j b‖ + ‖X a j‖ * ‖Y i b‖ := by
  have h := avm_ent_delta_le X Y i j (eI a) (eI b)
  simpa only [ent_eI_eI] using h

/-- The resolvent identity at the base point:
`G(W^{(ij),t}) = G(W) − (t − W_{ij}) G(W) Δ G(W^{(ij),t})`. -/
private lemma avm_res_base {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (t : ℝ) :
    GW A (Wupd Wm i j t) z = GW A Wm z +
      (-((t - Wm i j : ℝ) : ℂ)) • (GW A Wm z * deltaW i j * GW A (Wupd Wm i j t) z) := by
  have hid := avm_res_id hA hW hz i j (Wm i j) t
  rw [avm_Wupd_self hW] at hid
  rw [← hid]
  abel

private lemma avm_sq_add3 (u v w : ℝ) : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w)]

/-- The update of one entry: if `|G_{ab}| ≤ B`, `|G e_a|² ≤ L²` and `|t − W_{ij}| B ≤ 1/4`, then
`|G'_{ab}| ≤ 2B`, `|G' e_a|² ≤ (3L)²` and `|N⁻¹ tr G' − N⁻¹ tr G| ≤ 6 |t − W_{ij}| L² / N`, where
`G' = G(W^{(ij),t})`. -/
private lemma avm_pert {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) {B L : ℝ} (hL0 : 0 ≤ L)
    (hB : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hL : ∀ a, avmNsq (fun c => GW A Wm z c a) ≤ L ^ 2)
    {t : ℝ} (ht : |t - Wm i j| * B ≤ 1 / 4) :
    (∀ a b, ‖GW A (Wupd Wm i j t) z a b‖ ≤ 2 * B) ∧
      (∀ a, avmNsq (fun c => GW A (Wupd Wm i j t) z c a) ≤ (3 * L) ^ 2) ∧
      ‖mNW A (Wupd Wm i j t) z - mNW A Wm z‖ ≤ |t - Wm i j| * (6 * L ^ 2) / N := by
  set G := GW A Wm z with hG
  set G' := GW A (Wupd Wm i j t) z with hG'
  set d : ℝ := t - Wm i j with hd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i i)
  have hd0 : 0 ≤ |d| := abs_nonneg d
  have hrid : G' = G + (-(d : ℂ)) • (G * deltaW i j * G') := avm_res_base hA hW hz i j t
  have hent : ∀ a b, G' a b = G a b + (-(d : ℂ)) * (G * deltaW i j * G') a b := by
    intro a b
    conv_lhs => rw [hrid]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hentb : ∀ a b, ‖G' a b‖ ≤ ‖G a b‖ + |d| * (‖G a i‖ * ‖G' j b‖ + ‖G a j‖ * ‖G' i b‖) := by
    intro a b
    rw [hent a b]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (avm_entry_delta_le _ _ i j a b) hd0
  have hrow : ∀ a b, ‖G' a b‖ ≤ B + |d| * B * (‖G' i b‖ + ‖G' j b‖) := by
    intro a b
    have h1 := hentb a b
    have e1 : ‖G a i‖ * ‖G' j b‖ + ‖G a j‖ * ‖G' i b‖ ≤ B * (‖G' i b‖ + ‖G' j b‖) := by
      have := mul_le_mul_of_nonneg_right (hB a i) (norm_nonneg (G' j b))
      have := mul_le_mul_of_nonneg_right (hB a j) (norm_nonneg (G' i b))
      nlinarith
    have e2 := mul_le_mul_of_nonneg_left e1 hd0
    have := hB a b
    nlinarith
  have hM : ∀ b, ‖G' i b‖ + ‖G' j b‖ ≤ 4 * B := by
    intro b
    have h1 := hrow i b
    have h2 := hrow j b
    have hM0 : 0 ≤ ‖G' i b‖ + ‖G' j b‖ := by positivity
    have hq : 2 * (|d| * B) * (‖G' i b‖ + ‖G' j b‖) ≤ (‖G' i b‖ + ‖G' j b‖) / 2 := by
      have := mul_le_mul_of_nonneg_right ht hM0
      linarith
    nlinarith
  have hent2 : ∀ a b, ‖G' a b‖ ≤ 2 * B := by
    intro a b
    have h1 := hrow a b
    have h2 := mul_le_mul_of_nonneg_left (hM b) (mul_nonneg hd0 hB0)
    have h3 : |d| * B * (4 * B) ≤ B := by
      have := mul_le_mul_of_nonneg_right ht hB0
      linarith
    linarith
  have hcol : ∀ b, avmNsq (fun c => G' c b) ≤ (3 * L) ^ 2 := by
    intro b
    have hc : ∀ c, ‖G' c b‖ ≤ ‖G c b‖ + 2 * |d| * B * ‖G c i‖ + 2 * |d| * B * ‖G c j‖ := by
      intro c
      have h1 := hentb c b
      have e1 := mul_le_mul_of_nonneg_left (hent2 j b) (norm_nonneg (G c i))
      have e2 := mul_le_mul_of_nonneg_left (hent2 i b) (norm_nonneg (G c j))
      have e3 : |d| * (‖G c i‖ * ‖G' j b‖ + ‖G c j‖ * ‖G' i b‖) ≤
          |d| * (‖G c i‖ * (2 * B) + ‖G c j‖ * (2 * B)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hd0
      nlinarith
    have hsq : ∀ c, ‖G' c b‖ ^ 2 ≤ 3 * (‖G c b‖ ^ 2 + (2 * |d| * B) ^ 2 * ‖G c i‖ ^ 2 +
        (2 * |d| * B) ^ 2 * ‖G c j‖ ^ 2) := by
      intro c
      have h0 : 0 ≤ ‖G' c b‖ := norm_nonneg _
      have h1 := pow_le_pow_left₀ h0 (hc c) 2
      have h2 := avm_sq_add3 ‖G c b‖ (2 * |d| * B * ‖G c i‖) (2 * |d| * B * ‖G c j‖)
      nlinarith
    have hdB : (2 * |d| * B) ^ 2 ≤ 1 / 4 := by
      have h0 : 0 ≤ 2 * |d| * B := by positivity
      have : 2 * |d| * B ≤ 1 / 2 := by linarith
      nlinarith
    calc avmNsq (fun c => G' c b) = ∑ c, ‖G' c b‖ ^ 2 := rfl
      _ ≤ ∑ c, 3 * (‖G c b‖ ^ 2 + (2 * |d| * B) ^ 2 * ‖G c i‖ ^ 2 +
          (2 * |d| * B) ^ 2 * ‖G c j‖ ^ 2) := Finset.sum_le_sum fun c _ => hsq c
      _ = 3 * (avmNsq (fun c => G c b) + (2 * |d| * B) ^ 2 * avmNsq (fun c => G c i) +
          (2 * |d| * B) ^ 2 * avmNsq (fun c => G c j)) := by
          unfold avmNsq
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.mul_sum]
      _ ≤ 3 * (L ^ 2 + (1 / 4) * L ^ 2 + (1 / 4) * L ^ 2) := by
          have hb := hL b
          have hi := hL i
          have hj := hL j
          have hi0 := avmNsq_nonneg (fun c => G c i)
          have hj0 := avmNsq_nonneg (fun c => G c j)
          have k1 : (2 * |d| * B) ^ 2 * avmNsq (fun c => G c i) ≤ (1 / 4) * L ^ 2 :=
            mul_le_mul hdB hi hi0 (by norm_num)
          have k2 : (2 * |d| * B) ^ 2 * avmNsq (fun c => G c j) ≤ (1 / 4) * L ^ 2 :=
            mul_le_mul hdB hj hj0 (by norm_num)
          linarith
      _ ≤ (3 * L) ^ 2 := by nlinarith [sq_nonneg L]
  refine ⟨hent2, hcol, ?_⟩
  -- the trace
  have hsymm : ∀ a b, G' b a = G' a b := avm_GW_symm hA (avm_Wupd_symm hW i j t) z
  have htr : mNW A (Wupd Wm i j t) z - mNW A Wm z =
      (N : ℂ)⁻¹ * ((-(d : ℂ)) * ∑ c, (G * deltaW i j * G') c c) := by
    unfold mNW
    rw [← hG, ← hG', ← mul_sub, ← Matrix.trace_sub]
    congr 1
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.sub_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hent c c]
    ring
  have hcs1 : ∑ c, ‖G c i‖ * ‖G' c j‖ ≤ L * (3 * L) :=
    avm_cs (fun c => ‖G c i‖) (fun c => ‖G' c j‖) hL0 (by positivity) (hL i) (hcol j)
  have hcs2 : ∑ c, ‖G c j‖ * ‖G' c i‖ ≤ L * (3 * L) :=
    avm_cs (fun c => ‖G c j‖) (fun c => ‖G' c i‖) hL0 (by positivity) (hL j) (hcol i)
  have hsum : ‖∑ c, (G * deltaW i j * G') c c‖ ≤ 6 * L ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c, ‖(G * deltaW i j * G') c c‖
        ≤ ∑ c, (‖G c i‖ * ‖G' c j‖ + ‖G c j‖ * ‖G' c i‖) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h := avm_entry_delta_le G G' i j c c
          rw [hsymm c j, hsymm c i] at h
          exact h
      _ ≤ L * (3 * L) + L * (3 * L) := by rw [Finset.sum_add_distrib]; exact add_le_add hcs1 hcs2
      _ = 6 * L ^ 2 := by ring
  rw [htr, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_inv,
    Complex.norm_natCast]
  have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg N)
  calc (N : ℝ)⁻¹ * (|d| * ‖∑ c, (G * deltaW i j * G') c c‖) ≤ (N : ℝ)⁻¹ * (|d| * (6 * L ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hd0) hN0
    _ = |d| * (6 * L ^ 2) / N := by rw [div_eq_inv_mul]

end Pert

/-! ## The coefficients after the update of one entry -/

section CoeffPert

variable {N : ℕ}

/-- After the update `W → W^{(ij),t}`: `|a_0| ≤ F̃(W) + 6 |t − W_{ij}| L²/N` and
`|a_{k+1}| ≤ 4 (8B)^k (3L)²/N`. -/
private lemma avm_coeff_pert {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) {B L : ℝ} (hL0 : 0 ≤ L)
    (hB : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hL : ∀ a, avmNsq (fun c => GW A Wm z c a) ≤ L ^ 2)
    {t : ℝ} (ht : |t - Wm i j| * B ≤ 1 / 4) :
    ‖avgCoeffW A (Wupd Wm i j t) z i j 0‖ ≤ FtW A Wm z + |t - Wm i j| * (6 * L ^ 2) / N ∧
      ∀ k, ‖avgCoeffW A (Wupd Wm i j t) z i j (k + 1)‖ ≤
        4 * (4 * (2 * B)) ^ k * (3 * L) ^ 2 / N := by
  obtain ⟨h1, h2, h3⟩ := avm_pert hA hW hz i j hL0 hB hL ht
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i i)
  refine ⟨?_, fun k => ?_⟩
  · rw [avm_avgCoeff_zero]
    have e : mNW A (Wupd Wm i j t) z - mW (specOf A) z =
        (mNW A Wm z - mW (specOf A) z) + (mNW A (Wupd Wm i j t) z - mNW A Wm z) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl h3)
  · have hsym := avm_GW_symm hA (avm_Wupd_symm hW i j t) z
    exact avm_avgCoeff_le (by positivity) h1 (avm_H_le_of_col hsym (by positivity) h2) i j k

/-- After the update `W → W^{(ij),t}`:
`|f_n| ≤ (n+1)^p (8B+1)^n ((F̃(W) + 6 |t − W_{ij}| L²/N)^p + (36 L²/N)^p)`. -/
private lemma avm_f_pert {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) {B L : ℝ} (hL0 : 0 ≤ L)
    (hB : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hL : ∀ a, avmNsq (fun c => GW A Wm z c a) ≤ L ^ 2)
    {t : ℝ} (ht : |t - Wm i j| * B ≤ 1 / 4) (p n : ℕ) :
    ‖fCoeff p (avgCoeffW A (Wupd Wm i j t) z i j) n‖ ≤ ((n : ℝ) + 1) ^ p *
      ((8 * B + 1) ^ n * ((FtW A Wm z + |t - Wm i j| * (6 * L ^ 2) / N) ^ p +
        (36 * L ^ 2 / N) ^ p)) := by
  obtain ⟨h0, hk⟩ := avm_coeff_pert hA hW hz i j hL0 hB hL ht
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i i)
  have hF0 : 0 ≤ FtW A Wm z := norm_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine avm_fCoeff_le p n _ (by positivity) (by positivity) (by positivity) h0 fun k hk1 _ => ?_
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine (hk k').trans ?_
  have hpow : (8 * B) ^ k' ≤ (8 * B + 1) ^ (k' + 1) := by
    calc (8 * B) ^ k' ≤ (8 * B + 1) ^ k' := pow_le_pow_left₀ (by positivity) (by linarith) k'
      _ ≤ (8 * B + 1) ^ (k' + 1) :=
          pow_le_pow_right₀ (by linarith) (Nat.le_succ k')
  have hL2 : 0 ≤ 36 * L ^ 2 / N := by positivity
  calc 4 * (4 * (2 * B)) ^ k' * (3 * L) ^ 2 / N = (8 * B) ^ k' * (36 * L ^ 2 / N) := by ring
    _ ≤ (8 * B + 1) ^ (k' + 1) * (36 * L ^ 2 / N) := mul_le_mul_of_nonneg_right hpow hL2

end CoeffPert

/-! ## The event of the anisotropic bounds at all pairs `(e_a, e_b)` -/

section Event

variable {N : ℕ}

/-- The constant `2τ⁻²(1 + κ⁻¹) + 1`, `κ = (3τ⁻¹ + 1)⁻²`, of the column bound. -/
private def avmC1 (τ : ℝ) : ℝ := 2 * τ⁻¹ ^ 2 * (1 + (((3 * τ⁻¹ + 1) ^ 2)⁻¹)⁻¹) + 1

private lemma avmC1_pos {τ : ℝ} (hτ : 0 < τ) : 0 < avmC1 τ := by
  unfold avmC1
  have : 0 < τ⁻¹ := inv_pos.2 hτ
  positivity

/-- `κ η ≤ Im m` on `𝐃^W` for `‖A‖ ≤ τ⁻¹`. -/
private lemma avm_im_ge {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ} (hN : 1 ≤ N)
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) :
    ((3 * τ⁻¹ + 1) ^ 2)⁻¹ * z.im ≤ (mW (specOf A) z).im := by
  obtain ⟨hzim, hzE, -, hzη⟩ := hset.domain.1 hz
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i =>
    (abs_specOf_le_norm hset.symmA i).trans hset.normA
  exact im_mW_ge hN hset.pos ha hzim hzE hzη

/-- On the event `|(G − Π)_{ab}| ≤ e Ψ` for all `a, b`: `|G_{ab}| ≤ τ⁻¹ + 1`,
`|G e_a|² ≤ c₁ e N Ψ²` and `F̃ ≤ e Ψ`. -/
private lemma avm_on_event (hN : 1 ≤ N) {τ : ℝ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    {S : Set ℂ} (hset : WigSetting τ N A S) (hW : Wmᵀ = Wm) {z : ℂ} (hz : z ∈ S) {e : ℝ}
    (he : 1 ≤ e) (heΨ : e * PsiW (specOf A) z ≤ 1)
    (hE : ∀ a b, ‖(GW A Wm z - piW A z) a b‖ ≤ e * PsiW (specOf A) z) :
    (∀ a b, ‖GW A Wm z a b‖ ≤ τ⁻¹ + 1) ∧
      (∀ a, avmNsq (fun c => GW A Wm z c a) ≤ avmC1 τ * e * N * PsiW (specOf A) z ^ 2) ∧
      FtW A Wm z ≤ e * PsiW (specOf A) z := by
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  have hκ : 0 < ((3 * τ⁻¹ + 1) ^ 2)⁻¹ := by
    have : 0 < τ⁻¹ := inv_pos.2 hτ
    positivity
  have hPi : ∀ a b, ‖piW A z a b‖ ≤ τ⁻¹ := by
    intro a b
    have h := norm_piW_le hτ hset.symmA hset.standing hz (Pi.single a 1) (Pi.single b 1)
    rwa [avm_testBilin_single, avm_testNorm_single, avm_testNorm_single, mul_one,
      mul_one] at h
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · have e1 : GW A Wm z a b = (GW A Wm z - piW A z) a b + piW A z a b := by
      simp [Matrix.sub_apply]
    rw [e1]
    exact (norm_add_le _ _).trans (by linarith [hE a b, hPi a b])
  · have hv : ‖testBilin (Pi.single a 1) (GW A Wm z - piW A z) (Pi.single a 1)‖ ≤
        e * PsiW (specOf A) z * testNorm (Pi.single a (1 : ℝ)) ^ 2 := by
      rw [avm_testBilin_single, avm_testNorm_single, one_pow, mul_one]
      exact hE a a
    have h := avm_col_event hN hset.symmA hW hτ hset.standing hz hzim hκ
      (avm_im_ge hN hset hz) he (Pi.single a 1) hv
    rw [avm_col_eq, avm_testNorm_single, one_pow, mul_one] at h
    unfold avmC1
    exact h
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have htr := avm_trace_piW (A := A) hN hset.symmA hzim
    unfold FtW mNW
    rw [← htr, ← mul_sub, ← Matrix.trace_sub, norm_mul, norm_inv, Complex.norm_natCast,
      Matrix.trace]
    calc (N : ℝ)⁻¹ * ‖∑ a, Matrix.diag (GW A Wm z - piW A z) a‖
        ≤ (N : ℝ)⁻¹ * ∑ _a : Fin N, e * PsiW (specOf A) z :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun a _ => hE a a)) (inv_nonneg.2 hNr.le)
      _ = e * PsiW (specOf A) z := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

/-- The event of the anisotropic bounds at all pairs `(e_a, e_b)` has probability at least
`1 − N² N^{−D}`. -/
private lemma avm_event_prob {Ω : Type} [MeasureSpace Ω] {A : Matrix (Fin N) (Fin N) ℝ}
    {Y : Ω → Matrix (Fin N) (Fin N) ℝ} {z : ℂ} {ε Da : ℝ}
    (h : AnisotropicLawWAt N ε Da A Y {z}) :
    ℙ {ω | ∀ a b, ‖(GW A (Y ω) z - piW A z) a b‖ ≤
        (N : ℝ) ^ ε * PsiW (specOf A) z}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 * (N : ℝ) ^ (-Da)) := by
  have hP := avm_prob (fun a : Fin N => Pi.single a (1 : ℝ))
    (fun ω => GW A (Y ω) z - piW A z) (h z (Set.mem_singleton z))
  rw [Fintype.card_fin] at hP
  convert hP using 3
  ext ω
  simp only [Set.mem_ofPred_eq, avm_testBilin_single, avm_testNorm_single, mul_one]

end Event

/-! ## The remainder of the re-expansion -/

section Rem

variable {N : ℕ}

/-- `R_l = f_l(W) − ∑_{k ≤ 4p−l} C(l+k, l) W_{ij}^k f_{l+k}(W^{(ij),0})` for the averaged
coefficients. -/
private def avmRem (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N) (p l : ℕ) : ℂ :=
  fCoeff p (avgCoeffW A Wm z i j) l -
    ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * ((Wm i j : ℝ) : ℂ) ^ k *
      fCoeff p (avgCoeffW A (Wupd Wm i j 0) z i j) (l + k)

private lemma avm_measurable_rem (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N)
    (p l : ℕ) : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => avmRem A Wm z i j p l := by
  unfold avmRem
  refine (avm_measurable_fCoeff p l fun k => avm_measurable_res A z i j k).sub ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  refine (measurable_const.mul ?_).mul (avm_measurable_fUpd A z i j p (l + k) 0)
  exact (Complex.measurable_ofReal.comp (measurable_pi_iff.1
    (measurable_pi_iff.1 measurable_id i) j)).pow_const k

private lemma avm_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- The remainder on the event: from `|G_{ab}| ≤ B`, `|G e_a|² ≤ L²` and `8 |W_{ij}| B ≤ 1`,
`|R_l| ≤ (4p+1)! (4p+2)^p (8B+1)^{4p+1} (X^p + Y^p) |W_{ij}|^{4p+1−l}`, with
`X ≥ F̃ + 12 |W_{ij}| L²/N` and `Y ≥ 36 L²/N`. -/
private lemma avm_rem_good {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) {B L X Y : ℝ} (hL0 : 0 ≤ L)
    (hB : ∀ a b, ‖GW A Wm z a b‖ ≤ B) (hL : ∀ a, avmNsq (fun c => GW A Wm z c a) ≤ L ^ 2)
    (hξ : 2 * |Wm i j| * B ≤ 1 / 4)
    (hX : FtW A Wm z + 2 * |Wm i j| * (6 * L ^ 2) / N ≤ X) (hY : 36 * L ^ 2 / N ≤ Y)
    (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖avmRem A Wm z i j p l‖ ≤ ((4 * p + 1).factorial : ℝ) *
      ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p * ((8 * B + 1) ^ (4 * p + 1) * (X ^ p + Y ^ p))) *
      |Wm i j| ^ (4 * p - l + 1) := by
  have ha : ∀ k x, HasDerivAt (fun y => avgCoeffW A (Wupd Wm i j y) z i j k)
      (((k : ℂ) + 1) * avgCoeffW A (Wupd Wm i j x) z i j (k + 1)) x :=
    fun k x => avm_hasDerivAt_avgCoeffW hA hW hz i j k x
  have hidx : l + (4 * p - l) + 1 = 4 * p + 1 := by omega
  have hF0 : 0 ≤ FtW A Wm z := norm_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i i)
  have hY0 : 0 ≤ 36 * L ^ 2 / N := by positivity
  have hT := fCoeff_taylor p ha l (4 * p - l) 0 (Wm i j)
    ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p * ((8 * B + 1) ^ (4 * p + 1) * (X ^ p + Y ^ p)))
    (fun s hs => by
      rw [zero_add, hidx]
      have hs' := avm_abs_le_of_mem_uIcc hs
      have hd : |s - Wm i j| ≤ 2 * |Wm i j| := by
        calc |s - Wm i j| ≤ |s| + |Wm i j| := abs_sub _ _
          _ ≤ 2 * |Wm i j| := by linarith
      have ht : |s - Wm i j| * B ≤ 1 / 4 := by nlinarith
      have h := avm_f_pert hA hW hz i j hL0 hB hL ht p (4 * p + 1)
      refine h.trans ?_
      have hx : FtW A Wm z + |s - Wm i j| * (6 * L ^ 2) / N ≤ X := by
        refine le_trans ?_ hX
        have : |s - Wm i j| * (6 * L ^ 2) ≤ 2 * |Wm i j| * (6 * L ^ 2) :=
          mul_le_mul_of_nonneg_right hd (by positivity)
        have := div_le_div_of_nonneg_right this hN0
        linarith
      have hx0 : 0 ≤ FtW A Wm z + |s - Wm i j| * (6 * L ^ 2) / N := by positivity
      have h1 : (FtW A Wm z + |s - Wm i j| * (6 * L ^ 2) / N) ^ p ≤ X ^ p :=
        pow_le_pow_left₀ hx0 hx p
      have h2 : (36 * L ^ 2 / N) ^ p ≤ Y ^ p := pow_le_pow_left₀ hY0 hY p
      gcongr)
  rw [zero_add, hidx, avm_Wupd_self hW] at hT
  exact hT

/-- `|f_n(W)| ≤ 2 (4p+1)^p (4N)^{5p}` for `n ≤ 4p` and a symmetric `W`, when `η⁻¹ ≤ N`. -/
private lemma avm_f_det (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N) (i j : Fin N) (p n : ℕ)
    (hn : n ≤ 4 * p) :
    ‖fCoeff p (avgCoeffW A Wm z i j) n‖ ≤ 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) := by
  have h := avm_det_fCoeff hN hA hW hz i j p n
  refine h.trans ?_
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  have hn1 : (n : ℝ) + 1 ≤ ((4 * p + 1 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
    push_cast; linarith
  have h1 : (4 * z.im⁻¹) ^ n ≤ (4 * N) ^ (4 * p) :=
    (pow_le_pow_left₀ (by positivity) (by linarith) n).trans
      (pow_le_pow_right₀ (by linarith) hn)
  have h2 : (z.im⁻¹ + 1) ^ p ≤ (4 * N) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
  have h3 : z.im⁻¹ ^ p ≤ (4 * N) ^ p := pow_le_pow_left₀ hη (by linarith) p
  calc ((n : ℝ) + 1) ^ p * ((4 * z.im⁻¹) ^ n * ((z.im⁻¹ + 1) ^ p + z.im⁻¹ ^ p))
      ≤ ((4 * p + 1 : ℕ) : ℝ) ^ p * ((4 * N) ^ (4 * p) * ((4 * N) ^ p + (4 * N) ^ p)) := by
        gcongr
    _ = 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) := by
        rw [show 5 * p = 4 * p + p by ring, pow_add]; ring

/-- The constant `2 (4p+1)^p (1 + (4p+1) 2^{4p})` of the deterministic remainder bound. -/
private def avmKR (p : ℕ) : ℝ := 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (1 + (4 * p + 1) * 2 ^ (4 * p))

private lemma avmKR_nonneg (p : ℕ) : 0 ≤ avmKR p := by
  unfold avmKR; positivity

/-- The deterministic remainder bound `|R_l| ≤ K (4N)^{5p} (1 + |W_{ij}|^{4p})`. -/
private lemma avm_rem_det (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N)
    (i j : Fin N) (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖avmRem A Wm z i j p l‖ ≤ avmKR p * (4 * N) ^ (5 * p) * (1 + |Wm i j| ^ (4 * p)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set F : ℝ := 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) with hF
  have hF0 : 0 ≤ F := by positivity
  set X : ℝ := |Wm i j| with hX
  have hX0 : 0 ≤ X := abs_nonneg _
  have hW0 := avm_Wupd_symm hW i j 0
  have hterm : ∀ k ∈ Finset.range (4 * p - l + 1),
      ‖((l + k).choose l : ℂ) * ((Wm i j : ℝ) : ℂ) ^ k *
          fCoeff p (avgCoeffW A (Wupd Wm i j 0) z i j) (l + k)‖ ≤
        2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hc : ((l + k).choose l : ℝ) ≤ 2 ^ (4 * p) := by
      have := Nat.choose_le_two_pow (l + k) l
      have h2 : 2 ^ (l + k) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this.trans h2
    have hxk : X ^ k ≤ 1 + X ^ (4 * p) := by
      rcases le_total X 1 with h1 | h1
      · have : X ^ k ≤ 1 := pow_le_one₀ hX0 h1
        linarith [pow_nonneg hX0 (4 * p)]
      · have : X ^ k ≤ X ^ (4 * p) := pow_le_pow_right₀ h1 (by omega)
        linarith
    have hf := avm_f_det hN hA hW0 hz hηN i j p (l + k) (by omega)
    calc ((l + k).choose l : ℝ) * |Wm i j| ^ k *
          ‖fCoeff p (avgCoeffW A (Wupd Wm i j 0) z i j) (l + k)‖
        ≤ 2 ^ (4 * p) * (1 + X ^ (4 * p)) * F := by
          gcongr
      _ = 2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F) := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfl := avm_f_det hN hA hW hz hηN i j p l hl
  unfold avmRem
  refine (norm_sub_le _ _).trans ?_
  have hX1 : F ≤ (1 + X ^ (4 * p)) * F :=
    le_mul_of_one_le_left hF0 (by linarith [pow_nonneg hX0 (4 * p)])
  calc _ ≤ F + ((4 * p - l + 1 : ℕ) : ℝ) * (2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F)) :=
        add_le_add hfl hsum
    _ ≤ (1 + X ^ (4 * p)) * F + (4 * p + 1) * (2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F)) := by
        have hcard : ((4 * p - l + 1 : ℕ) : ℝ) ≤ 4 * p + 1 := by
          have : 4 * p - l + 1 ≤ 4 * p + 1 := by omega
          exact_mod_cast this
        gcongr
    _ = avmKR p * (4 * N) ^ (5 * p) * (1 + X ^ (4 * p)) := by
        unfold avmKR; rw [hF]; ring

end Rem

/-! ## Expectations: the re-expansion and Lemma 7.7 -/

/-- The moment constant `2 K_R² 4^{10p} (1 + max(C_{8p}, 0))`. -/
private def avmKM (p : ℕ) (C : ℕ → ℝ) : ℝ :=
  2 * avmKR p ^ 2 * 4 ^ (10 * p) * (1 + max (C (8 * p)) 0)

/-- Expectation of the re-expansion along `α = (i, j)`: by independence of `W_{ij}` and
`W^{(ij),0}`, `E f_l(W) = ∑_k C(l+k, l) E W_{ij}^k E f_{l+k}(W^{(ij),0}) + E R_l`; Lemma 7.7 bounds
`|E R_l| ≤ 2 N^δ Γ` on the event `|R_l| ≤ Γ`. -/
private lemma avm_expect {N : ℕ} (hN : 1 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N) {C : ℕ → ℝ}
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N)
    (p l : ℕ) (hl : l ≤ 4 * p) {δ D Γ : ℝ} (hδ : 0 ≤ δ) (hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ D)
    (hΓ : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ Γ) (hK : avmKM p C ≤ N)
    (hev : HighProbAt N D {ω | ‖avmRem A (W ω) z α.1.1 α.1.2 p l‖ ≤ Γ}) :
    (∫ ω, fCoeff p (avgCoeffW A (W ω) z α.1.1 α.1.2) l) =
      (∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
        (∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ k) *
        (∫ ω, fCoeff p (avgCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z α.1.1 α.1.2) (l + k))) +
        ∫ ω, avmRem A (W ω) z α.1.1 α.1.2 p l ∧
    ‖∫ ω, avmRem A (W ω) z α.1.1 α.1.2 p l‖ ≤ 2 * (N : ℝ) ^ δ * Γ := by
  set i := α.1.1 with hi
  set j := α.1.2 with hj
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hWm : Measurable W :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => hW.measurable a b
  have hξm : Measurable fun ω => W ω i j := hW.measurable i j
  set F0 : ℝ := 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) with hF0
  have hF0m : ∀ n, AEStronglyMeasurable fun ω =>
      fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) n :=
    fun n => ((avm_measurable_fUpd A z i j p n 0).comp hWm).aestronglyMeasurable
  have hFm : AEStronglyMeasurable fun ω => fCoeff p (avgCoeffW A (W ω) z i j) l :=
    ((avm_measurable_fCoeff p l fun k => avm_measurable_res A z i j k).comp
      hWm).aestronglyMeasurable
  have hF0b : ∀ n ≤ 4 * p, ∀ ω, ‖fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) n‖ ≤ F0 :=
    fun n hn ω => avm_f_det hN hA (avm_Wupd_symm (hW.symm ω) i j 0) hz hηN i j p n hn
  have hFb : ∀ ω, ‖fCoeff p (avgCoeffW A (W ω) z i j) l‖ ≤ F0 :=
    fun ω => avm_f_det hN hA (hW.symm ω) hz hηN i j p l hl
  have hFi : Integrable fun ω => fCoeff p (avgCoeffW A (W ω) z i j) l :=
    Integrable.of_bound hFm F0 (ae_of_all _ hFb)
  have hpowm : ∀ k : ℕ, Measurable fun t : ℝ => (t : ℂ) ^ k :=
    fun k => Complex.measurable_ofReal.pow_const k
  have hym' : ∀ k : ℕ, AEStronglyMeasurable fun ω => (W ω i j : ℂ) ^ k :=
    fun k => ((hpowm k).comp hξm).aestronglyMeasurable
  have hsq1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hN1r
  have habs : ∀ (x : ℝ) (k : ℕ), |x| ^ k ≤ |Real.sqrt N * x| ^ k := by
    intro x k
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (abs_nonneg x) hsq1
  have hyi : ∀ k : ℕ, Integrable fun ω => (W ω i j : ℂ) ^ k := by
    intro k
    refine (hW.integrable_moment k i j).mono' (hym' k) (ae_of_all _ fun ω => ?_)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact habs _ k
  have hprodi : ∀ k ∈ Finset.range (4 * p - l + 1), Integrable fun ω =>
      (W ω i j : ℂ) ^ k * fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) (l + k) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    exact (hyi k).mul_bdd (hF0m (l + k)) (ae_of_all _ (hF0b (l + k) (by omega)))
  have hprod : ∀ k : ℕ, ∫ ω, (W ω i j : ℂ) ^ k *
      fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) (l + k) =
      (∫ ω, (W ω i j : ℂ) ^ k) * ∫ ω, fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) (l + k) :=
    fun k => ((avm_indep hW α).symm.comp (hpowm k)
      (avm_measurable_fCoeff p (l + k) fun k' =>
        avm_measurable_res A z i j k')).integral_fun_mul_eq_mul_integral
      (hym' k) (hF0m (l + k))
  set Rf : Ω → ℂ := fun ω => avmRem A (W ω) z i j p l with hRf
  set Sf : Ω → ℂ := fun ω => ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
      ((W ω i j : ℂ) ^ k * fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) (l + k)) with hSf
  have hSi : Integrable Sf := integrable_finsetSum _ fun k hk => (hprodi k hk).const_mul _
  have hdec : ∀ ω, fCoeff p (avgCoeffW A (W ω) z i j) l = Sf ω + Rf ω := by
    intro ω
    simp only [hSf, hRf, avmRem]
    rw [Finset.sum_congr rfl fun k _ => (mul_assoc ((l + k).choose l : ℂ) ((W ω i j : ℂ) ^ k)
      (fCoeff p (avgCoeffW A (Wupd (W ω) i j 0) z i j) (l + k))).symm]
    ring
  have hRi : Integrable Rf := by
    have : Rf = fun ω => fCoeff p (avgCoeffW A (W ω) z i j) l - Sf ω := by
      funext ω; rw [hdec ω]; ring
    rw [this]; exact hFi.sub hSi
  refine ⟨?_, ?_⟩
  · calc (∫ ω, fCoeff p (avgCoeffW A (W ω) z i j) l)
        = ∫ ω, (Sf ω + Rf ω) := integral_congr_ae (ae_of_all _ hdec)
      _ = (∫ ω, Sf ω) + ∫ ω, Rf ω := integral_add hSi hRi
      _ = _ := by
          congr 1
          rw [hSf, integral_finsetSum _ fun k hk => (hprodi k hk).const_mul _]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, hprod k]
          ring
  · -- Lemma 7.7
    set KR := avmKR p with hKR
    have hKR0 : 0 ≤ KR := avmKR_nonneg p
    set Cr : ℝ := ((10 * p + 1 : ℕ) : ℝ) with hCr
    set C' : ℝ := max (C (8 * p)) 0 with hC'
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hRb : ∀ ω, ‖Rf ω‖ ≤ KR * (4 * N) ^ (5 * p) * (1 + |W ω i j| ^ (4 * p)) := fun ω =>
      avm_rem_det hN hA (hW.symm ω) hz hηN i j p l hl
    have hR2b : ∀ ω, ‖Rf ω‖ ^ 2 ≤
        2 * KR ^ 2 * (4 * N) ^ (10 * p) * (1 + |W ω i j| ^ (8 * p)) := by
      intro ω
      have h := pow_le_pow_left₀ (norm_nonneg _) (hRb ω) 2
      refine h.trans ?_
      set X := |W ω i j| ^ (4 * p) with hX
      have hX2 : |W ω i j| ^ (8 * p) = X ^ 2 := by rw [hX, ← pow_mul]; ring_nf
      have hN10 : ((4 : ℝ) * N) ^ (10 * p) = (((4 : ℝ) * N) ^ (5 * p)) ^ 2 := by
        rw [← pow_mul]; ring_nf
      rw [hX2, hN10]
      have hsq : (1 + X) ^ 2 ≤ 2 * (1 + X ^ 2) := by nlinarith [sq_nonneg (1 - X)]
      have hc : 0 ≤ (KR * ((4 : ℝ) * N) ^ (5 * p)) ^ 2 := sq_nonneg _
      calc (KR * (4 * (N : ℝ)) ^ (5 * p) * (1 + X)) ^ 2
          = (KR * ((4 : ℝ) * N) ^ (5 * p)) ^ 2 * (1 + X) ^ 2 := by ring
        _ ≤ (KR * ((4 : ℝ) * N) ^ (5 * p)) ^ 2 * (2 * (1 + X ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq hc
        _ = _ := by ring
    have hξ8m : AEStronglyMeasurable fun ω => |W ω i j| ^ (8 * p) :=
      (hξm.abs.pow_const _).aestronglyMeasurable
    have hξ8i : Integrable fun ω => |W ω i j| ^ (8 * p) :=
      (hW.integrable_moment (8 * p) i j).mono' hξ8m (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact habs _ _)
    have hξ8E : ∫ ω, |W ω i j| ^ (8 * p) ≤ C' :=
      (integral_mono hξ8i (hW.integrable_moment (8 * p) i j) fun ω => habs _ _).trans
        ((hW.moment (8 * p) i j).trans (le_max_left _ _))
    have hGi : Integrable fun ω => 2 * KR ^ 2 * (4 * (N : ℝ)) ^ (10 * p) *
        (1 + |W ω i j| ^ (8 * p)) := ((integrable_const 1).add hξ8i).const_mul _
    have hRm : AEStronglyMeasurable fun ω => ‖Rf ω‖ ^ 2 :=
      (((avm_measurable_rem A z i j p l).comp hWm).norm.pow_const 2).aestronglyMeasurable
    have hR2i : Integrable fun ω => ‖Rf ω‖ ^ 2 :=
      hGi.mono' hRm (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hR2b ω)
    have hR2E : ∫ ω, ‖Rf ω‖ ^ 2 ≤ (N : ℝ) ^ Cr := by
      calc ∫ ω, ‖Rf ω‖ ^ 2 ≤ ∫ ω, 2 * KR ^ 2 * (4 * (N : ℝ)) ^ (10 * p) *
            (1 + |W ω i j| ^ (8 * p)) := integral_mono hR2i hGi hR2b
        _ = 2 * KR ^ 2 * (4 * (N : ℝ)) ^ (10 * p) * (1 + ∫ ω, |W ω i j| ^ (8 * p)) := by
            rw [integral_const_mul, integral_add (integrable_const 1) hξ8i]
            simp
        _ ≤ 2 * KR ^ 2 * (4 * (N : ℝ)) ^ (10 * p) * (1 + C') := by gcongr
        _ = avmKM p C * (N : ℝ) ^ (10 * p) := by
            unfold avmKM; rw [mul_pow]; ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (10 * p) := by gcongr
        _ = (N : ℝ) ^ Cr := by
            rw [hCr, Real.rpow_natCast, pow_succ]; ring
    have hΓ0 : 0 ≤ Γ := (Real.rpow_nonneg hNp.le _).trans hΓ
    have hdom : DomAt N δ D (fun ω => ‖Rf ω‖) (fun _ => Γ) := by
      unfold DomAt
      unfold HighProbAt at hev
      refine le_trans (measure_mono fun ω hω => ?_) hev
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le] at hω ⊢
      have : Γ ≤ (N : ℝ) ^ δ * Γ := le_mul_of_one_le_left hΓ0 (Real.one_le_rpow hN1r hδ)
      exact lt_of_le_of_lt this hω
    have h77 := integral_le_of_domAt (ξ := fun ω => ‖Rf ω‖) hN hδ (C := Cr) hD hΓ
      (fun ω => norm_nonneg _) hR2i hR2E hdom
    exact (norm_integral_le_integral_norm _).trans h77

/-! ## Bounds on the event: the remainder and the coefficients at `W^{(ij),0}` -/

section EventBounds

variable {N : ℕ}

private lemma avm_add_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p : ℕ) :
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

/-- The constant `(4p+1)! (4p+2)^p (8(τ⁻¹+1)+1)^{4p+1} (2^p + (36 c₁)^p)` of the remainder on the
event. -/
private def avmKRg (τ : ℝ) (p : ℕ) : ℝ :=
  ((4 * p + 1).factorial : ℝ) * (((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
    (8 * (τ⁻¹ + 1) + 1) ^ (4 * p + 1) * (2 ^ p + (36 * avmC1 τ) ^ p)

/-- The constant `(4p+1)^p (8(τ⁻¹+1)+1)^{4p} 2^p (2^p + (36 c₁)^p)` of the coefficients at
`W^{(ij),0}` on the event. -/
private def avmKcr (τ : ℝ) (p : ℕ) : ℝ :=
  ((4 * p + 1 : ℕ) : ℝ) ^ p * (8 * (τ⁻¹ + 1) + 1) ^ (4 * p) * (2 ^ p * (1 + (36 * avmC1 τ) ^ p))

private lemma avmKcr_nonneg {τ : ℝ} (hτ : 0 < τ) (p : ℕ) : 0 ≤ avmKcr τ p := by
  unfold avmKcr
  have := avmC1_pos hτ
  have : 0 < τ⁻¹ := inv_pos.2 hτ
  positivity

/-- The square root `L = (c₁ e N Ψ²)^{1/2}` of the column bound. -/
private lemma avm_L_sq {τ e Ψ : ℝ} (hτ : 0 < τ) (he : 0 ≤ e) :
    0 ≤ Real.sqrt (avmC1 τ * e * N * Ψ ^ 2) ∧
      Real.sqrt (avmC1 τ * e * N * Ψ ^ 2) ^ 2 = avmC1 τ * e * N * Ψ ^ 2 := by
  have := avmC1_pos hτ
  exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (by positivity)⟩

/-- On the event and for `|W_{ij}| ≤ r` with `8 r (τ⁻¹+1) ≤ 1` and `12 r c₁ ≤ 1`:
`|R_l| ≤ K_R (e Ψ)^p r^{4p+1−l}`. -/
private lemma avm_rem_event (hN : 1 ≤ N) {τ : ℝ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    {S : Set ℂ} (hset : WigSetting τ N A S) (hW : Wmᵀ = Wm) {z : ℂ} (hz : z ∈ S) {e r : ℝ}
    (he : 1 ≤ e) (heΨ : e * PsiW (specOf A) z ≤ 1)
    (hE : ∀ a b, ‖(GW A Wm z - piW A z) a b‖ ≤ e * PsiW (specOf A) z) (i j : Fin N)
    (hr : |Wm i j| ≤ r) (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4) (hr2 : 12 * r * avmC1 τ ≤ 1)
    (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖avmRem A Wm z i j p l‖ ≤ avmKRg τ p * (e * PsiW (specOf A) z) ^ p * r ^ (4 * p - l + 1) := by
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  set Ψ := PsiW (specOf A) z with hΨ
  have hΨ0 : 0 ≤ Ψ := by
    have := (avm_psi (a := specOf A) hN hzim).1
    exact le_trans (by positivity) this
  have hΨ1 : Ψ ≤ 1 := by nlinarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hB, hL, hF⟩ := avm_on_event hN hset hW hz he heΨ hE
  obtain ⟨hL0, hLsq⟩ := avm_L_sq (N := N) (Ψ := Ψ) hτ (by linarith : (0 : ℝ) ≤ e)
  set L := Real.sqrt (avmC1 τ * e * N * Ψ ^ 2) with hLdef
  have hL' : ∀ a, avmNsq (fun c => GW A Wm z c a) ≤ L ^ 2 := fun a => by rw [hLsq]; exact hL a
  have hc1 := avmC1_pos hτ
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hr
  have hLN : L ^ 2 / N = avmC1 τ * e * Ψ ^ 2 := by rw [hLsq]; field_simp
  have hξ : 2 * |Wm i j| * (τ⁻¹ + 1) ≤ 1 / 4 := by
    have : 2 * |Wm i j| * (τ⁻¹ + 1) ≤ 2 * r * (τ⁻¹ + 1) := by
      have : 0 ≤ τ⁻¹ + 1 := by positivity
      nlinarith
    linarith
  have hX : FtW A Wm z + 2 * |Wm i j| * (6 * L ^ 2) / N ≤ 2 * (e * Ψ) := by
    have e1 : 2 * |Wm i j| * (6 * L ^ 2) / N = 12 * |Wm i j| * (L ^ 2 / N) := by ring
    rw [e1, hLN]
    have h1 : 12 * |Wm i j| * (avmC1 τ * e * Ψ ^ 2) ≤ 12 * r * avmC1 τ * (e * Ψ) * Ψ := by
      have : 0 ≤ avmC1 τ * e * Ψ ^ 2 := by positivity
      nlinarith
    have h2 : 12 * r * avmC1 τ * (e * Ψ) * Ψ ≤ e * Ψ := by
      have h3 : 0 ≤ e * Ψ := by positivity
      have h4 : 12 * r * avmC1 τ * (e * Ψ) ≤ e * Ψ := by nlinarith
      nlinarith
    linarith
  have hY : 36 * L ^ 2 / N ≤ 36 * avmC1 τ * (e * Ψ) := by
    have e1 : 36 * L ^ 2 / N = 36 * (L ^ 2 / N) := by ring
    rw [e1, hLN]
    have : 0 ≤ avmC1 τ * e * Ψ := by positivity
    nlinarith
  have h := avm_rem_good hset.symmA hW hzim i j hL0 hB hL' hξ hX hY p l hl
  refine h.trans ?_
  have hpow : |Wm i j| ^ (4 * p - l + 1) ≤ r ^ (4 * p - l + 1) :=
    pow_le_pow_left₀ (abs_nonneg _) hr _
  have hXY : (2 * (e * Ψ)) ^ p + (36 * avmC1 τ * (e * Ψ)) ^ p =
      (2 ^ p + (36 * avmC1 τ) ^ p) * (e * Ψ) ^ p := by
    rw [mul_pow, mul_pow]; ring
  rw [hXY]
  have hK0 : 0 ≤ ((4 * p + 1).factorial : ℝ) * ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
      ((8 * (τ⁻¹ + 1) + 1) ^ (4 * p + 1) * ((2 ^ p + (36 * avmC1 τ) ^ p) * (e * Ψ) ^ p))) := by
    have : 0 < τ⁻¹ := inv_pos.2 hτ
    positivity
  calc ((4 * p + 1).factorial : ℝ) * ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
        ((8 * (τ⁻¹ + 1) + 1) ^ (4 * p + 1) * ((2 ^ p + (36 * avmC1 τ) ^ p) * (e * Ψ) ^ p))) *
        |Wm i j| ^ (4 * p - l + 1)
      ≤ ((4 * p + 1).factorial : ℝ) * ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
        ((8 * (τ⁻¹ + 1) + 1) ^ (4 * p + 1) * ((2 ^ p + (36 * avmC1 τ) ^ p) * (e * Ψ) ^ p))) *
        r ^ (4 * p - l + 1) := mul_le_mul_of_nonneg_left hpow hK0
    _ = avmKRg τ p * (e * Ψ) ^ p * r ^ (4 * p - l + 1) := by unfold avmKRg; ring

/-- On the event and for `|W_{ij}| ≤ r` with `4 r (τ⁻¹+1) ≤ 1` and `6 r c₁ ≤ 1`, for `n ≤ 4p`:
`|f_n(W^{(ij),0})| ≤ K (F̃(W)^p + (e Ψ²)^p)`. -/
private lemma avm_crude_event (hN : 1 ≤ N) {τ : ℝ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    {S : Set ℂ} (hset : WigSetting τ N A S) (hW : Wmᵀ = Wm) {z : ℂ} (hz : z ∈ S) {e r : ℝ}
    (he : 1 ≤ e) (heΨ : e * PsiW (specOf A) z ≤ 1)
    (hE : ∀ a b, ‖(GW A Wm z - piW A z) a b‖ ≤ e * PsiW (specOf A) z) (i j : Fin N)
    (hr : |Wm i j| ≤ r) (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4) (hr2 : 12 * r * avmC1 τ ≤ 1)
    (p n : ℕ) (hn : n ≤ 4 * p) :
    ‖fCoeff p (avgCoeffW A (Wupd Wm i j 0) z i j) n‖ ≤
      avmKcr τ p * (FtW A Wm z ^ p + (e * PsiW (specOf A) z ^ 2) ^ p) := by
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  set Ψ := PsiW (specOf A) z with hΨ
  have hΨ0 : 0 ≤ Ψ := by
    have := (avm_psi (a := specOf A) hN hzim).1
    exact le_trans (by positivity) this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hB, hL, hF⟩ := avm_on_event hN hset hW hz he heΨ hE
  obtain ⟨hL0, hLsq⟩ := avm_L_sq (N := N) (Ψ := Ψ) hτ (by linarith : (0 : ℝ) ≤ e)
  set L := Real.sqrt (avmC1 τ * e * N * Ψ ^ 2) with hLdef
  have hL' : ∀ a, avmNsq (fun c => GW A Wm z c a) ≤ L ^ 2 := fun a => by rw [hLsq]; exact hL a
  have hc1 := avmC1_pos hτ
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hr
  have hLN : L ^ 2 / N = avmC1 τ * e * Ψ ^ 2 := by rw [hLsq]; field_simp
  have hT0 : 0 ≤ τ⁻¹ + 1 := by have := inv_pos.2 hτ; positivity
  have ht : |0 - Wm i j| * (τ⁻¹ + 1) ≤ 1 / 4 := by
    rw [zero_sub, abs_neg]
    nlinarith
  have h := avm_f_pert hset.symmA hW hzim i j hL0 hB hL' ht p n
  refine h.trans ?_
  have hF0 : 0 ≤ FtW A Wm z := norm_nonneg _
  have hx : FtW A Wm z + |0 - Wm i j| * (6 * L ^ 2) / N ≤ FtW A Wm z + e * Ψ ^ 2 := by
    rw [zero_sub, abs_neg]
    have e1 : |Wm i j| * (6 * L ^ 2) / N = 6 * |Wm i j| * (L ^ 2 / N) := by ring
    rw [e1, hLN]
    have : 0 ≤ avmC1 τ * e * Ψ ^ 2 := by positivity
    have h1 : 6 * |Wm i j| * (avmC1 τ * e * Ψ ^ 2) ≤ 6 * r * avmC1 τ * (e * Ψ ^ 2) := by
      nlinarith
    have h2 : 6 * r * avmC1 τ * (e * Ψ ^ 2) ≤ e * Ψ ^ 2 := by
      have : 0 ≤ e * Ψ ^ 2 := by positivity
      nlinarith
    linarith
  have hx0 : 0 ≤ FtW A Wm z + |0 - Wm i j| * (6 * L ^ 2) / N := by positivity
  have hy : 36 * L ^ 2 / N = 36 * avmC1 τ * (e * Ψ ^ 2) := by
    rw [show 36 * L ^ 2 / N = 36 * (L ^ 2 / N) by ring, hLN]; ring
  have heΨ2 : 0 ≤ e * Ψ ^ 2 := by positivity
  have h1 : (FtW A Wm z + |0 - Wm i j| * (6 * L ^ 2) / N) ^ p ≤
      2 ^ p * (FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p) :=
    (pow_le_pow_left₀ hx0 hx p).trans (avm_add_pow_le hF0 heΨ2 p)
  have h2 : (36 * L ^ 2 / N) ^ p = (36 * avmC1 τ) ^ p * (e * Ψ ^ 2) ^ p := by
    rw [hy, mul_pow]
  have hn1 : (n : ℝ) + 1 ≤ ((4 * p + 1 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
    push_cast; linarith
  have hlam : (8 * (τ⁻¹ + 1) + 1) ^ n ≤ (8 * (τ⁻¹ + 1) + 1) ^ (4 * p) :=
    pow_le_pow_right₀ (by linarith) hn
  have hS : (FtW A Wm z + |0 - Wm i j| * (6 * L ^ 2) / N) ^ p + (36 * L ^ 2 / N) ^ p ≤
      2 ^ p * (1 + (36 * avmC1 τ) ^ p) * (FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p) := by
    rw [h2]
    have hp1 : (e * Ψ ^ 2) ^ p ≤ FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p :=
      le_add_of_nonneg_left (pow_nonneg hF0 p)
    have hc0 : 0 ≤ (36 * avmC1 τ) ^ p := by positivity
    have h3 : (36 * avmC1 τ) ^ p * (e * Ψ ^ 2) ^ p ≤
        (36 * avmC1 τ) ^ p * (FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p) :=
      mul_le_mul_of_nonneg_left hp1 hc0
    have h4 : (36 * avmC1 τ) ^ p ≤ 2 ^ p * (36 * avmC1 τ) ^ p :=
      le_mul_of_one_le_left hc0 (one_le_pow₀ (by norm_num))
    have h5 : 0 ≤ FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p := by positivity
    nlinarith
  have hS0 : 0 ≤ (FtW A Wm z + |0 - Wm i j| * (6 * L ^ 2) / N) ^ p + (36 * L ^ 2 / N) ^ p := by
    positivity
  calc ((n : ℝ) + 1) ^ p * ((8 * (τ⁻¹ + 1) + 1) ^ n *
        ((FtW A Wm z + |0 - Wm i j| * (6 * L ^ 2) / N) ^ p + (36 * L ^ 2 / N) ^ p))
      ≤ ((4 * p + 1 : ℕ) : ℝ) ^ p * ((8 * (τ⁻¹ + 1) + 1) ^ (4 * p) *
        (2 ^ p * (1 + (36 * avmC1 τ) ^ p) * (FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p))) := by
        gcongr
    _ = avmKcr τ p * (FtW A Wm z ^ p + (e * Ψ ^ 2) ^ p) := by unfold avmKcr; ring

end EventBounds

/-! ## The event for a matrix of the class -/

section ClassEvent

variable {N : ℕ}

/-- The bad event has probability at most `(N² + 1) N^{−D}`. -/
private lemma avm_bad_prob {Ω : Type} [MeasureSpace Ω] {Ξ M : Set Ω} {Da : ℝ}
    (hΞ : ℙ Ξᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * (N : ℝ) ^ (-Da)))
    (hM : ℙ Mᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-Da))) :
    ℙ (Ξ ∩ M)ᶜ ≤ ENNReal.ofReal (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da)) := by
  have h0 : 0 ≤ (N : ℝ) ^ (-Da) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [Set.compl_inter]
  calc ℙ (Ξᶜ ∪ Mᶜ) ≤ ℙ Ξᶜ + ℙ Mᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * (N : ℝ) ^ (-Da)) + ENNReal.ofReal ((N : ℝ) ^ (-Da)) :=
        add_le_add hΞ hM
    _ = ENNReal.ofReal (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da)) := by
        rw [← ENNReal.ofReal_add (by positivity) h0]
        congr 1
        ring

/-- `(N² + 1) N^{−D} ≤ N^{−(D−3)}` for `N ≥ 2`. -/
private lemma avm_bad_le (hN : 2 ≤ N) (Da : ℝ) :
    ((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da) ≤ (N : ℝ) ^ (-(Da - 3)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have e : (N : ℝ) ^ (-(Da - 3)) = (N : ℝ) ^ 3 * (N : ℝ) ^ (-Da) := by
    rw [show -(Da - 3) = (3 : ℝ) + -Da by ring, Real.rpow_add hNp]
    norm_cast
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hNp.le _)
  nlinarith

/-- The remainder event for a matrix `Y` of the class satisfying the anisotropic law at `z`, with
`|Y_{ij}| ≤ r` with high probability: `|R_l| ≤ Γ` with probability `≥ 1 − N^{−(D−3)}`. -/
private lemma avm_rem_prob (hN : 2 ≤ N) {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) {Ω : Type} [MeasureSpace Ω]
    {Y : Ω → Matrix (Fin N) (Fin N) ℝ} (hYs : ∀ ω, (Y ω)ᵀ = Y ω) {εa Da r Γ : ℝ}
    (hAL : AnisotropicLawWAt N εa Da A Y {z}) (hεa : 0 ≤ εa)
    (heΨ : (N : ℝ) ^ εa * PsiW (specOf A) z ≤ 1) (i j : Fin N)
    (hmk : HighProbAt N Da {ω | |Y ω i j| ≤ r}) (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4)
    (hr2 : 12 * r * avmC1 τ ≤ 1) (p l : ℕ) (hl : l ≤ 4 * p)
    (hΓ : avmKRg τ p * ((N : ℝ) ^ εa * PsiW (specOf A) z) ^ p * r ^ (4 * p - l + 1) ≤ Γ) :
    HighProbAt N (Da - 3) {ω | ‖avmRem A (Y ω) z i j p l‖ ≤ Γ} := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set Ξ : Set Ω := {ω | ∀ a b, ‖(GW A (Y ω) z - piW A z) a b‖ ≤
    (N : ℝ) ^ εa * PsiW (specOf A) z} with hΞ
  set M : Set Ω := {ω | |Y ω i j| ≤ r} with hM
  have hbad := avm_bad_prob (avm_event_prob hAL) hmk
  unfold HighProbAt
  refine le_trans (measure_mono ?_) (hbad.trans (ENNReal.ofReal_le_ofReal (avm_bad_le hN Da)))
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
  intro hωΞM
  have h := avm_rem_event hN1 hset (hYs ω) hz (Real.one_le_rpow hNr hεa) heΨ hωΞM.1 i j
    hωΞM.2 hr1 hr2 p l hl
  linarith

/-- The coefficients at `Y^{(ij),0}` for a matrix `Y` of the class satisfying the anisotropic law
at `z`: `E |f_n(Y^{(ij),0})| ≤ K (E F̃(Y)^p + (e Ψ²)^p) + M (N² + 1) N^{−D}`. -/
private lemma avm_crude_E (hN : 2 ≤ N) {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) (hηN : z.im⁻¹ ≤ N) {Ω : Type}
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ}
    {Y : Ω → Matrix (Fin N) (Fin N) ℝ} (hY : WigClassEntries C N Y) {εa Da r : ℝ}
    (hAL : AnisotropicLawWAt N εa Da A Y {z}) (hεa : 0 ≤ εa)
    (heΨ : (N : ℝ) ^ εa * PsiW (specOf A) z ≤ 1) (i j : Fin N)
    (hmk : HighProbAt N Da {ω | |Y ω i j| ≤ r}) (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4)
    (hr2 : 12 * r * avmC1 τ ≤ 1) (p n : ℕ) (hn : n ≤ 4 * p) :
    ∫ ω, ‖fCoeff p (avgCoeffW A (Wupd (Y ω) i j 0) z i j) n‖ ≤
      avmKcr τ p * ((∫ ω, FtW A (Y ω) z ^ p) +
        ((N : ℝ) ^ εa * PsiW (specOf A) z ^ 2) ^ p) +
      2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) *
        (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da)) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  set Ξ : Set Ω := {ω | ∀ a b, ‖(GW A (Y ω) z - piW A z) a b‖ ≤
    (N : ℝ) ^ εa * PsiW (specOf A) z} with hΞ
  set M : Set Ω := {ω | |Y ω i j| ≤ r} with hM
  have hbad := avm_bad_prob (avm_event_prob hAL) hmk
  have hbadR : (ℙ (Ξ ∩ M)ᶜ).toReal ≤ ((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  have hWm : Measurable Y := measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b =>
    hY.measurable a b
  have hFm : Measurable fun ω => FtW A (Y ω) z ^ p :=
    ((avm_measurable_Ft A z).comp hWm).pow_const p
  have hFi : Integrable fun ω => FtW A (Y ω) z ^ p :=
    Integrable.of_bound hFm.aestronglyMeasurable ((z.im⁻¹ + 1) ^ p) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (show 0 ≤ FtW A (Y ω) z from norm_nonneg _) p)]
      exact pow_le_pow_left₀ (norm_nonneg _) (avm_FtW_le hN1 hset.symmA (hY.symm ω) hzim) p)
  set c : ℝ := ((N : ℝ) ^ εa * PsiW (specOf A) z ^ 2) ^ p with hc
  have hc0 : 0 ≤ c := by
    have := (avm_psi (a := specOf A) hN1 hzim).1
    have : 0 ≤ PsiW (specOf A) z := le_trans (by positivity) this
    positivity
  have hK0 := avmKcr_nonneg hτ p
  have hsplit := avm_split_int (Ξ := Ξ ∩ M)
    (Z := fun ω => ‖fCoeff p (avgCoeffW A (Wupd (Y ω) i j 0) z i j) n‖)
    (g := fun ω => avmKcr τ p * (FtW A (Y ω) z ^ p + c))
    (M := 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p)) (by positivity)
    (fun ω => norm_nonneg _) ((hFi.add (integrable_const c)).const_mul _)
    (fun ω => mul_nonneg hK0 (add_nonneg (pow_nonneg (norm_nonneg _) p) hc0))
    (fun ω hω => avm_crude_event hN1 hset (hY.symm ω) hz (Real.one_le_rpow hNr hεa) heΨ hω.1
      i j hω.2 hr1 hr2 p n hn)
    (fun ω => avm_f_det hN1 hset.symmA (avm_Wupd_symm (hY.symm ω) i j 0) hzim hηN i j p n hn)
  have hint : ∫ ω, avmKcr τ p * (FtW A (Y ω) z ^ p + c) =
      avmKcr τ p * ((∫ ω, FtW A (Y ω) z ^ p) + c) := by
    rw [integral_const_mul, integral_add hFi (integrable_const c), integral_const]
    simp
  rw [hint] at hsplit
  have hM0 : 0 ≤ 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * (N : ℝ)) ^ (5 * p) := by positivity
  exact hsplit.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbadR hM0))

end ClassEvent

/-! ## The expansion of one Lindeberg term -/

section Pair

variable {N : ℕ}

/-- One Lindeberg term for `F̃^p`: for the pair matrix with the entry `α` drawn from `ρ`,
`E F̃^p = ∑_{k ≤ 4p} E y^k · E f_k(W^{θ,(α),0}) + R` with `|R| ≤ 2 N^{−2} Ψ^{2p}`. -/
private lemma avm_pair_expand (hN : 2 ≤ N) {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) (hηN : z.im⁻¹ ≤ N) {C : ℕ → ℝ}
    {p : ℕ} (hp : Even p) {εa Da r : ℝ} (hεa : 0 ≤ εa)
    (heΨ : (N : ℝ) ^ εa * PsiW (specOf A) z ≤ 1) (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4)
    (hr2 : 12 * r * avmC1 τ ≤ 1) (hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ Da - 3)
    (hΓ0 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p))
    (hrem : avmKRg τ p * ((N : ℝ) ^ εa * PsiW (specOf A) z) ^ p * r ^ (4 * p - 0 + 1) ≤
      (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p))
    (hKM : avmKM p (momMaxW C) ≤ N) (Q : ModelClassW N)
    (hAL : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (Y : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N Y → Q Ω' Y →
      AnisotropicLawWAt N εa Da A Y {z})
    (hmk : ∀ {Ω' : Type} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (y : Ω' → ℝ), (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
        ∫ ω, |Real.sqrt N * y ω| ^ q ≤ momMaxW C q) →
      HighProbAt N Da {ω | |y ω| ≤ r})
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (hW : WigClassEntries (momMaxW C) N W)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (α : UpperIdx N) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : AvmULaw N (momMaxW C) (1 / N) (avmVarHi N α) ρ)
    (hQ : Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α ρ)) ofUpper) :
    ∃ R : ℂ, ‖R‖ ≤ 2 * ((N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p)) ∧
      ((∫ x, FtW A (ofUpper x) z ^ p ∂(interpLawAt θ (goeLaw N) (entryLawW W) α ρ) : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (4 * p + 1), (∫ y, (y : ℂ) ^ k ∂ρ) *
          (∫ x, fCoeff p (avgCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z α.1.1 α.1.2) k
            ∂(interpLaw θ (goeLaw N) (entryLawW W))) + R := by
  have hN1 : 1 ≤ N := by omega
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  -- the pair space
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := avm_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := avm_entryLawW_prob hW.measurable
  set ν := avmPairLaw θ (goeLaw N) (entryLawW W) α ρ with hν
  have : ∀ β, IsProbabilityMeasure (ν β) := avm_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
  have : IsProbabilityMeasure (ℙ : Measure (AvmPi N ν)) := avm_isProb_pi ν
  have hY : WigClassEntries (momMaxW C) (Ω := AvmPi N ν) N ofUpper :=
    avm_class_pair hN1 hW hθ.1 hθ.2 α ρ hρ
  have hALY := hAL (AvmPi N ν) ofUpper hY hQ
  have hξ := hmk (Ω' := AvmPi N ν)
    (fun ω => (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2)
    (fun q => ⟨hY.integrable_moment q _ _, hY.moment q _ _⟩)
  have hev := avm_rem_prob hN hset hz hY.symm hALY hεa heΨ α.1.1 α.1.2 hξ hr1 hr2 p 0
    (Nat.zero_le _) hrem
  obtain ⟨hexp, hR⟩ := avm_expect hN1 hset.symmA hzim hηN hY α p 0 (Nat.zero_le _)
    (le_refl (0 : ℝ)) hD hΓ0 hKM hev
  refine ⟨∫ ω : AvmPi N ν, avmRem A (ofUpper ω) z α.1.1 α.1.2 p 0, ?_, ?_⟩
  · refine hR.trans (le_of_eq ?_)
    simp
  · -- the left side
    have hL : ((∫ x, FtW A (ofUpper x) z ^ p ∂(interpLawAt θ (goeLaw N) (entryLawW W) α ρ) : ℝ)
        : ℂ) = ∫ ω : AvmPi N ν, fCoeff p (avgCoeffW A (ofUpper ω) z α.1.1 α.1.2) 0 := by
      simp_rw [avm_fCoeff_zero_eq hp]
      rw [integral_complex_ofReal]
      rfl
    rw [hL, hexp]
    congr 1
    simp only [Nat.sub_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 4 * p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hmom : ∫ ω : AvmPi N ν, ((ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2 : ℂ) ^ k =
        ∫ y, (y : ℂ) ^ k ∂ρ := by
      have h := avm_integral_coord ν α (f := fun y : ℝ => (y : ℂ) ^ k) (by fun_prop)
      have hνα : ν α = ρ := by simp [hν, avmPairLaw]
      rw [hνα] at h
      refine Eq.trans ?_ h
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have e : (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2 =
          (show UpperIdx N → ℝ from ω) α := by
        change (show UpperIdx N → ℝ from ω) (avmUp α.1.1 α.1.2) = _
        rw [avm_up_self]
      simp only [e]
    have hm : Measurable fun x : UpperIdx N → ℝ =>
        fCoeff p (avgCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z α.1.1 α.1.2) k :=
      (avm_measurable_fUpd A z α.1.1 α.1.2 p k 0).comp avm_measurable_ofUpper
    have hB : ∀ x : UpperIdx N → ℝ,
        ‖fCoeff p (avgCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z α.1.1 α.1.2) k‖ ≤
          2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) := fun x =>
      avm_f_det hN1 hset.symmA (avm_Wupd_symm (avm_ofUpper_symm x) _ _ 0) hzim hηN
        α.1.1 α.1.2 p k hk'
    have hinv : ∀ (x : UpperIdx N → ℝ) (t : ℝ),
        fCoeff p (avgCoeffW A (Wupd (ofUpper (Function.update x α t)) α.1.1 α.1.2 0) z
          α.1.1 α.1.2) k =
        fCoeff p (avgCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z α.1.1 α.1.2) k := by
      intro x t
      rw [avm_Wupd_ofUpper_update]
    have hcoef : ∫ ω : AvmPi N ν,
        fCoeff p (avgCoeffW A (Wupd (ofUpper ω) α.1.1 α.1.2 0) z α.1.1 α.1.2) k =
        ∫ x, fCoeff p (avgCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z α.1.1 α.1.2) k
          ∂(interpLaw θ (goeLaw N) (entryLawW W)) :=
      avm_integral_inv (θ := θ) (ρ₀ := goeLaw N) (ρ₁ := entryLawW W) α ρ hm hB hinv
    rw [hmom, hcoef]

end Pair

/-! ## The derivative of `θ ↦ E F̃^p(W^θ)` -/

section Deriv

variable {N : ℕ}

/-- The constant `L = 2^{4p} ∑_{k ≤ 4p} max(C_k, 0)`. -/
private def avmL (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  2 ^ (4 * p) * ∑ k ∈ Finset.range (4 * p + 1), max (C k) 0

private lemma avmL_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ avmL C p := by
  unfold avmL
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => le_max_right _ _)

/-- `∑_{k ≤ 4p} (2 C_k + 1)`. -/
private def avmCs (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (4 * p + 1), (2 * momMaxW C k + 1)

private lemma avm_ck_le_Cs (C : ℕ → ℝ) {p k : ℕ} (hk : k ≤ 4 * p) :
    2 * momMaxW C k + 1 ≤ avmCs C p := by
  unfold avmCs
  exact Finset.single_le_sum (f := fun k => 2 * momMaxW C k + 1)
    (fun j _ => by have := avm_momMaxW_nonneg C j; linarith) (Finset.mem_range.2 (by omega))

private lemma avmCs_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ avmCs C p :=
  le_trans (by have := avm_momMaxW_nonneg C 0; linarith) (avm_ck_le_Cs C (p := p) (k := 0)
    (Nat.zero_le _))

/-- The constant of the derivative bound. -/
private def avmKd (τ : ℝ) (p : ℕ) (C : ℕ → ℝ) (K3 : ℝ) : ℝ :=
  (4 * p + 1) * (avmCs C p * (avmKcr τ p + 1) + (2 * momMaxW C 3 + 1) *
    (K3 + avmL (momMaxW C) p * (avmKcr τ p + 1) + 2)) + 4

private lemma avmKd_nonneg {τ : ℝ} (hτ : 0 < τ) (p : ℕ) (C : ℕ → ℝ) {K3 : ℝ} (hK3 : 0 ≤ K3) :
    0 ≤ avmKd τ p C K3 := by
  unfold avmKd
  have := avmKcr_nonneg hτ p
  have := avmCs_nonneg C p
  have := avmL_nonneg (momMaxW C) p
  have := avm_momMaxW_nonneg C 3
  positivity

private lemma avm_choose_le {k m p : ℕ} (h : k + m ≤ 4 * p) :
    ((k + m).choose k : ℝ) ≤ 2 ^ (4 * p) := by
  have := Nat.choose_le_two_pow (k + m) k
  have h2 : 2 ^ (k + m) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) h
  exact_mod_cast this.trans h2

/-- The Lindeberg derivative bound for `F̃^p`: `|d/dθ E F̃^p(W^θ)| ≤ K (b + E F̃^p(W^θ))` with
`b = (N^δ Ψ²)^p + (N^{−c₀/2} (Nη)⁻¹)^p`, at a fixed `N` satisfying the numerical conditions. -/
private lemma avm_deriv_bound (hN : 2 ≤ N) {τ c₀ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) (hηN : z.im⁻¹ ≤ N) {C : ℕ → ℝ}
    {p : ℕ} (hp : Even p) (hp2 : 2 ≤ p) {εa Da r δ K3 : ℝ} (hεa : 0 ≤ εa) (hK3 : 0 ≤ K3)
    (heΨ : (N : ℝ) ^ εa * PsiW (specOf A) z ≤ 1) (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4)
    (hr2 : 12 * r * avmC1 τ ≤ 1) (hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ Da - 3)
    (hrem : ∀ l ≤ 4 * p, avmKRg τ p * ((N : ℝ) ^ εa * PsiW (specOf A) z) ^ p *
      r ^ (4 * p - l + 1) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p))
    (hΓ0 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p))
    (hKM : avmKM p (momMaxW C) ≤ N)
    (hoff : 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) *
      (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da)) ≤ ((N : ℝ) ^ εa * PsiW (specOf A) z ^ 2) ^ p)
    (heδ : (N : ℝ) ^ εa ≤ (N : ℝ) ^ δ) (Q : ModelClassW N)
    (hAL : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (Y : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N Y → Q Ω' Y →
      AnisotropicLawWAt N εa Da A Y {z})
    (hmk : ∀ {Ω' : Type} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (y : Ω' → ℝ), (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
        ∫ ω, |Real.sqrt N * y ω| ^ q ≤ momMaxW C q) →
      HighProbAt N Da {ω | |y ω| ≤ r})
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (hW : WigClassEntries (momMaxW C) N W)
    (hQ1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      Q (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper)
    (hQ2 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ α : UpperIdx N,
      Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α (entryLawW W α))) ofUpper ∧
      Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α (goeLaw N α))) ofUpper)
    (h3 : (∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0) ∨
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ s : UpperIdx N → ℂ, (∀ α, ‖s α‖ ≤ 1) →
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α *
          ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
            fCoeff p (avgCoeffW A (ofUpper ω) z α.1.1 α.1.2) 3‖ ≤
          K3 * (((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p +
            ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p +
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              FtW A (ofUpper ω) z ^ p)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      |∑ α : UpperIdx N,
        ((∫ x, FtW A (ofUpper x) z ^ p
            ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α))) -
          ∫ x, FtW A (ofUpper x) z ^ p
            ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α)))| ≤
        avmKd τ p C K3 * ((((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p +
          ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) +
          ∫ x, FtW A (ofUpper x) z ^ p ∂(interpLaw θ (goeLaw N) (entryLawW W))) := by
  intro θ hθ
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := avm_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := avm_entryLawW_prob hW.measurable
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (goeLaw N β) (entryLawW W β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (goeLaw N) (entryLawW W)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure
      (ℙ : Measure (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W))) := hIP
  have hWθ : WigClassEntries (momMaxW C)
      (Ω := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) N ofUpper :=
    avm_class_interp hN1 hW hθ.1 hθ.2
  have hALθ := hAL (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ (hQ1 θ hθ)
  -- notation
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨτ : τ / N ≤ Ψ := avm_psi_ge hN1 hτ _ (hset.domain.1 hz)
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨτ
  set b : ℝ := ((N : ℝ) ^ δ * Ψ ^ 2) ^ p + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p with hb
  have hb2 : 0 ≤ ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p := by positivity
  set eΨ2 : ℝ := ((N : ℝ) ^ εa * Ψ ^ 2) ^ p with heΨ2
  have heΨ20 : 0 ≤ eΨ2 := by positivity
  have heΨ2b : eΨ2 ≤ b := by
    have h1 : (N : ℝ) ^ εa * Ψ ^ 2 ≤ (N : ℝ) ^ δ * Ψ ^ 2 :=
      mul_le_mul_of_nonneg_right heδ (sq_nonneg _)
    have := pow_le_pow_left₀ (by positivity) h1 p
    linarith
  have hb0 : 0 ≤ b := heΨ20.trans heΨ2b
  have hΨ2p : Ψ ^ (2 * p) ≤ eΨ2 := by
    rw [heΨ2, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ p
    exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow hN1r hεa)
  set Φθ : ℝ := ∫ x, FtW A (ofUpper x) z ^ p ∂(interpLaw θ (goeLaw N) (entryLawW W))
    with hΦθ
  have hΦθ0 : 0 ≤ Φθ := integral_nonneg fun x => pow_nonneg (norm_nonneg _) p
  set Kcr := avmKcr τ p with hKcr
  have hKcr0 : 0 ≤ Kcr := avmKcr_nonneg hτ p
  set Zb : ℝ := (Kcr + 1) * (Φθ + b) with hZb
  have hZb0 : 0 ≤ Zb := by positivity
  -- the coefficients at `W^{θ,(α),0}`
  set Z : UpperIdx N → ℕ → ℂ := fun α k =>
    ∫ x, fCoeff p (avgCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z α.1.1 α.1.2) k
      ∂(interpLaw θ (goeLaw N) (entryLawW W)) with hZdef
  have hZbd : ∀ α k, k ≤ 4 * p → ‖Z α k‖ ≤ Zb := by
    intro α k hk
    have hξ := hmk (Ω' := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W))
      (fun ω => (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2)
      (fun q => ⟨hWθ.integrable_moment q _ _, hWθ.moment q _ _⟩)
    have hc := avm_crude_E hN hset hz hηN hWθ hALθ hεa heΨ α.1.1 α.1.2 hξ hr1 hr2 p k hk
    have hc' : ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
        ‖fCoeff p (avgCoeffW A (Wupd (ofUpper ω) α.1.1 α.1.2 0) z α.1.1 α.1.2) k‖ ≤ Zb := by
      refine hc.trans ?_
      have hE : (∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
          FtW A (ofUpper ω) z ^ p) = Φθ := rfl
      rw [hE]
      have h1 : Kcr * (Φθ + eΨ2) ≤ Kcr * (Φθ + b) :=
        mul_le_mul_of_nonneg_left (by linarith) hKcr0
      have h2 : Φθ + b ≥ b := by linarith
      rw [hZb]
      nlinarith
    exact (norm_integral_le_integral_norm _).trans hc'
  -- the expansions of the Lindeberg terms
  set Γ0 : ℝ := (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * Ψ ^ (2 * p) with hΓ0def
  have hexp : ∀ (α : UpperIdx N) (b : Bool), ∃ R : ℂ, ‖R‖ ≤ 2 * Γ0 ∧
      ((∫ x, FtW A (ofUpper x) z ^ p ∂(interpLawAt θ (goeLaw N) (entryLawW W) α
          (if b then entryLawW W α else goeLaw N α)) : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (4 * p + 1),
          (∫ y, (y : ℂ) ^ k ∂(if b then entryLawW W α else goeLaw N α)) * Z α k + R := by
    intro α b
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact avm_pair_expand hN hset hz hηN hp hεa heΨ hr1 hr2 hD hΓ0 (hrem 0 (Nat.zero_le _))
        hKM Q hAL hmk W hW θ hθ α (goeLaw N α) (avm_goeLaw_uLaw hN1 C α) (hQ2 θ hθ α).2
    · simp only [↓reduceIte]
      exact avm_pair_expand hN hset hz hηN hp hεa heΨ hr1 hr2 hD hΓ0 (hrem 0 (Nat.zero_le _))
        hKM Q hAL hmk W hW θ hθ α (entryLawW W α) (avm_entryLawW_uLaw hW α) (hQ2 θ hθ α).1
  choose R hRb hReq using hexp
  -- moments of the two entry laws
  set μ : Bool → UpperIdx N → ℕ → ℂ := fun b α k =>
    ∫ y, (y : ℂ) ^ k ∂(if b then entryLawW W α else goeLaw N α) with hμ
  have hlaw : ∀ (b : Bool) (α : UpperIdx N),
      AvmULaw N (momMaxW C) (1 / N) (avmVarHi N α) (if b then entryLawW W α else goeLaw N α) := by
    intro b α
    cases b
    · exact avm_goeLaw_uLaw hN1 C α
    · exact avm_entryLawW_uLaw hW α
  have hprob : ∀ (b : Bool) (α : UpperIdx N),
      IsProbabilityMeasure (if b then entryLawW W α else goeLaw N α) := by
    intro b α; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance
  have hmom : ∀ b α, (μ b α 0 = 1) ∧ (μ b α 1 = 0) ∧
      (α.1.1 ≠ α.1.2 → μ b α 2 = 1 / N) ∧
      ∀ k, ‖μ b α k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * momMaxW C k := by
    intro b α
    have := hprob b α
    obtain ⟨h0, h1, h2, h4⟩ := avm_law_mom hN1 (hlaw b α)
    refine ⟨h0, h1, fun hne => ?_, h4⟩
    have e := h2 (by simp [avmVarHi, hne])
    simp only [hμ]
    rw [e]
    push_cast
    ring
  set c : ℕ → ℝ := fun k => 2 * momMaxW C k + 1 with hc
  have hc1 : ∀ k, 1 ≤ c k := fun k => by
    have := avm_momMaxW_nonneg C k; simp only [hc]; linarith
  set d : UpperIdx N → ℕ → ℂ := fun α k => μ true α k - μ false α k with hd
  have hd01 : ∀ α, d α 0 = 0 ∧ d α 1 = 0 := by
    intro α
    simp only [hd, (hmom true α).1, (hmom false α).1, (hmom true α).2.1, (hmom false α).2.1]
    simp
  have hdk : ∀ α k, ‖d α k‖ ≤ c k * (N : ℝ) ^ (-(k : ℝ) / 2) := by
    intro α k
    have h1 := (hmom true α).2.2.2 k
    have h2 := (hmom false α).2.2.2 k
    have hN0 : 0 ≤ (N : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg hNp.le _
    calc ‖d α k‖ ≤ ‖μ true α k‖ + ‖μ false α k‖ := norm_sub_le _ _
      _ ≤ 2 * momMaxW C k * (N : ℝ) ^ (-(k : ℝ) / 2) := by linarith
      _ ≤ c k * (N : ℝ) ^ (-(k : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hN0
          simp only [hc]; linarith
  have hd2 : ∀ α : UpperIdx N, α.1.1 ≠ α.1.2 → d α 2 = 0 := by
    intro α hne
    simp only [hd, (hmom true α).2.2.1 hne, (hmom false α).2.2.1 hne, sub_self]
  have hd3 : (∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0) → ∀ α, d α 3 = 0 := by
    intro h α
    have e1 : μ true α 3 = 0 := by
      simp only [hμ, ↓reduceIte]
      rw [show (fun y : ℝ => (y : ℂ) ^ 3) = fun y : ℝ => ((y ^ 3 : ℝ) : ℂ) by
        funext y; push_cast; rfl, integral_complex_ofReal, h α]
      simp
    have e0 : μ false α 3 = 0 := by
      simp only [hμ, Bool.false_eq_true, ↓reduceIte]
      rw [show (fun y : ℝ => (y : ℂ) ^ 3) = fun y : ℝ => ((y ^ 3 : ℝ) : ℂ) by
        funext y; push_cast; rfl, integral_complex_ofReal]
      have : ∫ y, y ^ 3 ∂(goeLaw N α) = 0 := avm_integral_cube_gaussianReal _
      rw [this]
      simp
    simp only [hd, e1, e0, sub_self]
  -- the derivative as a double sum
  have hder : ((∑ α : UpperIdx N,
      ((∫ x, FtW A (ofUpper x) z ^ p
          ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α))) -
        ∫ x, FtW A (ofUpper x) z ^ p
          ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α))) : ℝ) : ℂ) =
      (∑ k ∈ Finset.Ico 2 (4 * p + 1), ∑ α : UpperIdx N, d α k * Z α k) +
        ∑ α : UpperIdx N, (R α true - R α false) := by
    push_cast
    have e : ∀ α : UpperIdx N,
        ((∫ x, FtW A (ofUpper x) z ^ p
            ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α)) : ℝ) : ℂ) -
          ((∫ x, FtW A (ofUpper x) z ^ p
            ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α)) : ℝ) : ℂ) =
        (∑ k ∈ Finset.range (4 * p + 1), d α k * Z α k) + (R α true - R α false) := by
      intro α
      have e1 := hReq α true
      have e0 := hReq α false
      simp only [↓reduceIte, Bool.false_eq_true] at e1 e0
      rw [e1, e0]
      simp only [hd, hμ, ↓reduceIte, Bool.false_eq_true, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [Finset.sum_congr rfl fun α _ => e α, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ 4 * p + 1)]
    have h01 : ∑ k ∈ Finset.range 2, ∑ α : UpperIdx N, d α k * Z α k = 0 := by
      simp [Finset.sum_range_succ, (hd01 _).1, (hd01 _).2]
    rw [h01, zero_add]
  -- the constants
  set K1 : ℝ := avmCs C p * (Kcr + 1) + (2 * momMaxW C 3 + 1) *
    (K3 + avmL (momMaxW C) p * (Kcr + 1) + 2) with hK1
  have hCs0 := avmCs_nonneg C p
  have hL0 := avmL_nonneg (momMaxW C) p
  have hm30 := avm_momMaxW_nonneg C 3
  have hK1a : avmCs C p * (Kcr + 1) ≤ K1 := by
    have : 0 ≤ (2 * momMaxW C 3 + 1) * (K3 + avmL (momMaxW C) p * (Kcr + 1) + 2) := by
      positivity
    linarith
  have hcard := avm_card_upper N
  -- the bound for each order `k ∈ [2, 4p]`
  have hord : ∀ k ∈ Finset.Ico 2 (4 * p + 1), ‖∑ α : UpperIdx N, d α k * Z α k‖ ≤
      K1 * (b + Φθ) := by
    intro k hk
    obtain ⟨hk2, hk4⟩ := Finset.mem_Ico.1 hk
    have hk4' : k ≤ 4 * p := Nat.lt_succ_iff.1 hk4
    have hck := avm_ck_le_Cs C hk4'
    have hgen : ‖∑ α : UpperIdx N, d α k * Z α k‖ ≤ ∑ α : UpperIdx N, ‖d α k‖ * Zb := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hZbd α k hk4') (norm_nonneg _)
    have hZbK : (c k) * Zb ≤ K1 * (b + Φθ) := by
      have : c k * Zb ≤ avmCs C p * Zb := mul_le_mul_of_nonneg_right hck hZb0
      have e : avmCs C p * Zb = avmCs C p * (Kcr + 1) * (b + Φθ) := by rw [hZb]; ring
      have h2 : avmCs C p * (Kcr + 1) * (b + Φθ) ≤ K1 * (b + Φθ) :=
        mul_le_mul_of_nonneg_right hK1a (by linarith)
      linarith
    rcases Nat.lt_or_ge k 4 with hk4l | hk4g
    · interval_cases k
      · -- k = 2: the diagonal
        have hs2 : ∀ α : UpperIdx N, ‖d α 2‖ * Zb ≤
            if α.1.1 = α.1.2 then c 2 * (N : ℝ)⁻¹ * Zb else 0 := by
          intro α
          by_cases hα : α.1.1 = α.1.2
          · rw [ite_eq_left hα]
            have := hdk α 2
            rw [avm_rpow_neg_one_half_two] at this
            exact mul_le_mul_of_nonneg_right this hZb0
          · rw [ite_eq_right hα, hd2 α hα, norm_zero, zero_mul]
        have hsum := hgen.trans (Finset.sum_le_sum fun α _ => hs2 α)
        rw [avm_sum_diag (fun _ => c 2 * (N : ℝ)⁻¹ * Zb)] at hsum
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
        have e : (N : ℝ) * (c 2 * (N : ℝ)⁻¹ * Zb) = c 2 * Zb := by field_simp
        rw [e] at hsum
        exact hsum.trans hZbK
      · -- k = 3: the third-order term
        rcases h3 with h3l | h3r
        · have hs0 : ∀ α, d α 3 = 0 := hd3 h3l
          simp only [hs0, zero_mul, Finset.sum_const_zero, norm_zero]
          exact mul_nonneg (le_trans (by positivity) hK1a) (by linarith)
        · -- the weights
          set w : ℝ := (N : ℝ) ^ ((3 : ℝ) / 2) / c 3 with hw
          have hc3 : 0 < c 3 := zero_lt_one.trans_le (hc1 3)
          have hw0 : 0 ≤ w := by positivity
          set s : UpperIdx N → ℂ := fun α => (w : ℂ) * d α 3 with hs
          have hN3 : (N : ℝ) ^ ((3 : ℝ) / 2) * (N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) = 1 := by
            rw [← Real.rpow_add hNp]; norm_num
          have hs1 : ∀ α, ‖s α‖ ≤ 1 := by
            intro α
            simp only [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
            calc w * ‖d α 3‖ ≤ w * (c 3 * (N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left (hdk α 3) hw0
              _ = 1 := by
                  rw [hw, div_mul_eq_mul_div, mul_comm (c 3), ← mul_assoc, hN3, one_mul,
                    div_self hc3.ne']
          have hds : ∀ α, d α 3 = ((c 3 * (N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * s α := by
            intro α
            simp only [hs, hw]
            rw [← mul_assoc, ← Complex.ofReal_mul]
            have : c 3 * (N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) * ((N : ℝ) ^ ((3 : ℝ) / 2) / c 3) = 1 := by
              rw [mul_div_assoc', mul_comm (c 3), mul_assoc, mul_comm (c 3), ← mul_assoc,
                mul_comm ((N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)), hN3, one_mul, div_self hc3.ne']
            rw [this]; simp
          -- the transfer from `W^{θ,(α),0}` to `W^θ`
          set Γ3 : ℝ := (N : ℝ) ^ (((3 : ℕ) : ℝ) / 2 - 2) * Ψ ^ (2 * p) with hΓ3def
          have hΓ3 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ Γ3 := by
            refine hΓ0.trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; linarith)
          have hp3 : 3 ≤ 4 * p := by omega
          have hexp3 : ∀ α : UpperIdx N,
              (∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                fCoeff p (avgCoeffW A (ofUpper ω) z α.1.1 α.1.2) 3) =
                (∑ k ∈ Finset.range (4 * p - 3 + 1), ((3 + k).choose 3 : ℂ) *
                  (∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                    ((ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2 : ℂ) ^ k) *
                  Z α (3 + k)) +
                ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                  avmRem A (ofUpper ω) z α.1.1 α.1.2 p 3 ∧
              ‖∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                  avmRem A (ofUpper ω) z α.1.1 α.1.2 p 3‖ ≤ 2 * Γ3 := by
            intro α
            have hξ := hmk (Ω' := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W))
              (fun ω => (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2)
              (fun q => ⟨hWθ.integrable_moment q _ _, hWθ.moment q _ _⟩)
            have hev := avm_rem_prob hN hset hz hWθ.symm hALθ hεa heΨ α.1.1 α.1.2 hξ hr1 hr2
              p 3 hp3 (hrem 3 hp3)
            obtain ⟨h1, h2⟩ := avm_expect hN1 hset.symmA hzim hηN hWθ α p 3 hp3
              (le_refl (0 : ℝ)) hD hΓ3 hKM hev
            refine ⟨h1, h2.trans (le_of_eq ?_)⟩
            simp
          -- the moments of the entries of `W^θ`
          set μθ : UpperIdx N → ℕ → ℂ := fun α k =>
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              ((ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2 : ℂ) ^ k with hμθ
          have hμθ0 : ∀ α, μθ α 0 = 1 := fun α => by simp [hμθ]
          have hμθ1 : ∀ α, μθ α 1 = 0 := by
            intro α
            simp only [hμθ, pow_one]
            rw [integral_complex_ofReal, hWθ.mean]
            simp
          have hμθk : ∀ α k, ‖μθ α k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * max (momMaxW C k) 0 :=
            fun α k => avm_moment_entry hWθ hN1 _ _ k
          set X : UpperIdx N → ℂ := fun α =>
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              fCoeff p (avgCoeffW A (ofUpper ω) z α.1.1 α.1.2) 3 with hX
          set T : UpperIdx N → ℂ := fun α => ∑ k ∈ Finset.Ico 2 (4 * p - 3 + 1),
            ((3 + k).choose 3 : ℂ) * μθ α k * Z α (3 + k) with hT
          set ER : UpperIdx N → ℂ := fun α =>
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              avmRem A (ofUpper ω) z α.1.1 α.1.2 p 3 with hER
          have hZ3 : ∀ α, Z α 3 = X α - T α - ER α := by
            intro α
            have h := (hexp3 α).1
            rw [← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ 4 * p - 3 + 1)] at h
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
            have e0 : μθ α 0 = 1 := hμθ0 α
            have e1 : μθ α 1 = 0 := hμθ1 α
            change X α = _ at h
            simp only [hμθ] at e0 e1
            rw [e0, e1] at h
            simp only [hT, hER, hμθ]
            norm_num at h
            rw [h]
            ring
          -- the bounds on `T` and `ER`
          have hN1' : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := Real.rpow_neg_one _
          have hTb : ∀ α, ‖T α‖ ≤ (N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) := by
            intro α
            refine (norm_sum_le _ _).trans ?_
            have hterm : ∀ k ∈ Finset.Ico 2 (4 * p - 3 + 1),
                ‖((3 + k).choose 3 : ℂ) * μθ α k * Z α (3 + k)‖ ≤
                  2 ^ (4 * p) * ((N : ℝ)⁻¹ * (max (momMaxW C k) 0 * Zb)) := by
              intro k hk
              obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.1 hk
              rw [norm_mul, norm_mul, Complex.norm_natCast]
              have hc := avm_choose_le (k := 3) (m := k) (p := p) (by omega)
              have hm := hμθk α k
              have hNk : (N : ℝ) ^ (-(k : ℝ) / 2) ≤ (N : ℝ)⁻¹ := by
                rw [← hN1']
                refine Real.rpow_le_rpow_of_exponent_le hN1r ?_
                have : (2 : ℝ) ≤ k := by exact_mod_cast hk1
                linarith
              have hz := hZbd α (3 + k) (by omega)
              have hm0 : 0 ≤ max (momMaxW C k) 0 := le_max_right _ _
              calc ((3 + k).choose 3 : ℝ) * ‖μθ α k‖ * ‖Z α (3 + k)‖
                  ≤ 2 ^ (4 * p) * ((N : ℝ)⁻¹ * max (momMaxW C k) 0) * Zb := by
                    gcongr
                    exact hm.trans (mul_le_mul_of_nonneg_right hNk hm0)
                _ = 2 ^ (4 * p) * ((N : ℝ)⁻¹ * (max (momMaxW C k) 0 * Zb)) := by ring
            refine (Finset.sum_le_sum hterm).trans ?_
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
            have hsub : ∑ k ∈ Finset.Ico 2 (4 * p - 3 + 1), max (momMaxW C k) 0 ≤
                ∑ k ∈ Finset.range (4 * p + 1), max (momMaxW C k) 0 :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun k hk => Finset.mem_range.2 (by
                  have := (Finset.mem_Ico.1 hk).2; omega))
                (fun k _ _ => le_max_right _ _)
            have : 2 ^ (4 * p) * ((N : ℝ)⁻¹ *
                ((∑ k ∈ Finset.Ico 2 (4 * p - 3 + 1), max (momMaxW C k) 0) * Zb)) ≤
                2 ^ (4 * p) * ((N : ℝ)⁻¹ *
                ((∑ k ∈ Finset.range (4 * p + 1), max (momMaxW C k) 0) * Zb)) := by
              gcongr
            refine this.trans (le_of_eq ?_)
            unfold avmL
            ring
          have hERb : ∀ α, ‖ER α‖ ≤ 2 * Γ3 := fun α => (hexp3 α).2
          -- the weighted sum
          have hsplitZ : ∑ α : UpperIdx N, s α * Z α 3 =
              ∑ α : UpperIdx N, s α * X α - ∑ α : UpperIdx N, s α * (T α + ER α) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [hZ3 α]
            ring
          have hX3 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * X α‖ ≤ K3 * (b + Φθ) := by
            have h := h3r θ hθ s hs1
            have hE : (∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                FtW A (ofUpper ω) z ^ p) = Φθ := rfl
            rw [hE] at h
            refine h.trans (le_of_eq ?_)
            rw [hb]
          have hTE : ‖∑ α : UpperIdx N, s α * (T α + ER α)‖ ≤
              (N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3) := by
            refine (norm_sum_le _ _).trans ?_
            calc ∑ α : UpperIdx N, ‖s α * (T α + ER α)‖
                ≤ ∑ _α : UpperIdx N, ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3) := by
                  refine Finset.sum_le_sum fun α _ => ?_
                  rw [norm_mul]
                  have h1 := (norm_add_le (T α) (ER α)).trans (add_le_add (hTb α) (hERb α))
                  have h0 : 0 ≤ ‖T α + ER α‖ := norm_nonneg _
                  calc ‖s α‖ * ‖T α + ER α‖ ≤ 1 * ‖T α + ER α‖ :=
                        mul_le_mul_of_nonneg_right (hs1 α) h0
                    _ ≤ _ := by rw [one_mul]; exact h1
              _ = (Fintype.card (UpperIdx N) : ℝ) *
                  ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              _ ≤ (N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3) :=
                  mul_le_mul_of_nonneg_right hcard (by positivity)
          have hN32 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 *
              ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3)) ≤
              avmL (momMaxW C) p * Zb + 2 * Ψ ^ (2 * p) := by
            have e1 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 * (N : ℝ)⁻¹) =
                (N : ℝ) ^ (-(1 : ℝ) / 2) := by
              rw [show (N : ℝ) ^ 2 * (N : ℝ)⁻¹ = (N : ℝ) ^ (1 : ℝ) by
                rw [Real.rpow_one]; field_simp, ← Real.rpow_add hNp]
              norm_num
            have e2 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 * Γ3) = Ψ ^ (2 * p) := by
              rw [hΓ3def, show (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
              rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
              norm_num
            have h12 : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
            have hLZ : 0 ≤ avmL (momMaxW C) p * Zb := mul_nonneg hL0 hZb0
            calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 *
                  ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3))
                = ((N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 * (N : ℝ)⁻¹)) *
                    (avmL (momMaxW C) p * Zb) +
                  2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 * Γ3)) := by ring
              _ = (N : ℝ) ^ (-(1 : ℝ) / 2) * (avmL (momMaxW C) p * Zb) + 2 * Ψ ^ (2 * p) := by
                  rw [e1, e2]
              _ ≤ 1 * (avmL (momMaxW C) p * Zb) + 2 * Ψ ^ (2 * p) := by
                  gcongr
              _ = avmL (momMaxW C) p * Zb + 2 * Ψ ^ (2 * p) := by rw [one_mul]
          have hN32' : (N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) = (N : ℝ) ^ (-(3 : ℝ) / 2) := by norm_num
          have hsum_eq : ∑ α : UpperIdx N, d α 3 * Z α 3 =
              ((c 3 * (N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
                ∑ α : UpperIdx N, s α * Z α 3 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [hds α, mul_assoc]
          have hS3 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * Z α 3‖ ≤
              K3 * (b + Φθ) + (avmL (momMaxW C) p * Zb + 2 * Ψ ^ (2 * p)) := by
            rw [hsplitZ]
            have hN0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hNp.le _
            calc (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * X α -
                  ∑ α : UpperIdx N, s α * (T α + ER α)‖
                ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * (‖∑ α : UpperIdx N, s α * X α‖ +
                  ‖∑ α : UpperIdx N, s α * (T α + ER α)‖) :=
                  mul_le_mul_of_nonneg_left (norm_sub_le _ _) hN0
              _ = (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * X α‖ +
                  (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * (T α + ER α)‖ := by ring
              _ ≤ K3 * (b + Φθ) + (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ 2 *
                  ((N : ℝ)⁻¹ * (avmL (momMaxW C) p * Zb) + 2 * Γ3)) :=
                  add_le_add hX3 (mul_le_mul_of_nonneg_left hTE hN0)
              _ ≤ K3 * (b + Φθ) + (avmL (momMaxW C) p * Zb + 2 * Ψ ^ (2 * p)) :=
                  add_le_add le_rfl hN32
          rw [hsum_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity), hN32']
          have hc30 : 0 ≤ c 3 := le_trans zero_le_one (hc1 3)
          have hfin : K3 * (b + Φθ) + (avmL (momMaxW C) p * Zb + 2 * Ψ ^ (2 * p)) ≤
              (K3 + avmL (momMaxW C) p * (Kcr + 1) + 2) * (b + Φθ) := by
            have e : avmL (momMaxW C) p * Zb = avmL (momMaxW C) p * (Kcr + 1) * (b + Φθ) := by
              rw [hZb]; ring
            rw [e]
            have : 2 * Ψ ^ (2 * p) ≤ 2 * (b + Φθ) := by linarith only [hΨ2p, heΨ2b, hΦθ0]
            linarith only [this]
          have hK1b : (2 * momMaxW C 3 + 1) * (K3 + avmL (momMaxW C) p * (Kcr + 1) + 2) ≤ K1 := by
            have : 0 ≤ avmCs C p * (Kcr + 1) := by positivity
            rw [hK1]; linarith only [this]
          calc c 3 * (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * Z α 3‖
              = c 3 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α * Z α 3‖) := by ring
            _ ≤ c 3 * ((K3 + avmL (momMaxW C) p * (Kcr + 1) + 2) * (b + Φθ)) :=
                mul_le_mul_of_nonneg_left (hS3.trans hfin) hc30
            _ = (2 * momMaxW C 3 + 1) * (K3 + avmL (momMaxW C) p * (Kcr + 1) + 2) * (b + Φθ) := by
                simp only [hc]; ring
            _ ≤ K1 * (b + Φθ) := mul_le_mul_of_nonneg_right hK1b (by linarith only [hb0, hΦθ0])
    · -- k ≥ 4
      have hs4 : ∀ α : UpperIdx N, ‖d α k‖ * Zb ≤ c k * (N : ℝ) ^ (-(k : ℝ) / 2) * Zb :=
        fun α => mul_le_mul_of_nonneg_right (hdk α k) hZb0
      have hsum := hgen.trans (Finset.sum_le_sum fun α _ => hs4 α)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      have hNk : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(k : ℝ) / 2) ≤ 1 := by
        rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_add hNp]
        refine Real.rpow_le_one_of_one_le_of_nonpos hN1r ?_
        have : (4 : ℝ) ≤ k := by exact_mod_cast hk4g
        push_cast; linarith
      have hck0 : 0 ≤ c k * Zb := mul_nonneg (le_trans zero_le_one (hc1 k)) hZb0
      have : (Fintype.card (UpperIdx N) : ℝ) * (c k * (N : ℝ) ^ (-(k : ℝ) / 2) * Zb) ≤
          c k * Zb := by
        have e : (Fintype.card (UpperIdx N) : ℝ) * (c k * (N : ℝ) ^ (-(k : ℝ) / 2) * Zb) =
            ((Fintype.card (UpperIdx N) : ℝ) * (N : ℝ) ^ (-(k : ℝ) / 2)) * (c k * Zb) := by ring
        rw [e]
        have h1 : (Fintype.card (UpperIdx N) : ℝ) * (N : ℝ) ^ (-(k : ℝ) / 2) ≤ 1 :=
          (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hNp.le _)).trans hNk
        calc ((Fintype.card (UpperIdx N) : ℝ) * (N : ℝ) ^ (-(k : ℝ) / 2)) * (c k * Zb)
            ≤ 1 * (c k * Zb) := mul_le_mul_of_nonneg_right h1 hck0
          _ = c k * Zb := one_mul _
      exact (hsum.trans this).trans hZbK
  -- the remainders
  have hrem' : ‖∑ α : UpperIdx N, (R α true - R α false)‖ ≤ 4 * b := by
    have h1 : ∀ α, ‖R α true - R α false‖ ≤ 4 * Γ0 :=
      fun α => (norm_sub_le _ _).trans (by linarith [hRb α true, hRb α false])
    have h2 : (N : ℝ) ^ 2 * Γ0 = Ψ ^ (2 * p) := by
      rw [hΓ0def, show (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      rw [← mul_assoc, ← Real.rpow_add hNp]
      norm_num
    calc ‖∑ α : UpperIdx N, (R α true - R α false)‖
        ≤ ∑ α : UpperIdx N, ‖R α true - R α false‖ := norm_sum_le _ _
      _ ≤ ∑ _α : UpperIdx N, 4 * Γ0 := Finset.sum_le_sum fun α _ => h1 α
      _ = (Fintype.card (UpperIdx N) : ℝ) * (4 * Γ0) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ 2 * (4 * Γ0) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 4 * Ψ ^ (2 * p) := by rw [← h2]; ring
      _ ≤ 4 * b := by linarith
  -- assembly
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hder]
  have hsumk : ‖∑ k ∈ Finset.Ico 2 (4 * p + 1), ∑ α : UpperIdx N, d α k * Z α k‖ ≤
      (4 * p + 1) * (K1 * (b + Φθ)) := by
    calc _ ≤ ∑ k ∈ Finset.Ico 2 (4 * p + 1), ‖∑ α : UpperIdx N, d α k * Z α k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.Ico 2 (4 * p + 1), K1 * (b + Φθ) := Finset.sum_le_sum hord
      _ = ((Finset.Ico 2 (4 * p + 1)).card : ℝ) * (K1 * (b + Φθ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * p + 1) * (K1 * (b + Φθ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_trans (by positivity) hK1a)
            (by linarith))
          rw [Nat.card_Ico]
          have : 4 * p + 1 - 2 ≤ 4 * p + 1 := by omega
          exact_mod_cast this
  have hK10 : 0 ≤ K1 := le_trans (by positivity) hK1a
  calc _ ≤ ‖∑ k ∈ Finset.Ico 2 (4 * p + 1), ∑ α : UpperIdx N, d α k * Z α k‖ +
        ‖∑ α : UpperIdx N, (R α true - R α false)‖ := norm_add_le _ _
    _ ≤ (4 * p + 1) * (K1 * (b + Φθ)) + 4 * b := add_le_add hsumk hrem'
    _ ≤ (4 * p + 1) * (K1 * (b + Φθ)) + 4 * (b + Φθ) :=
        add_le_add le_rfl (by linarith only [hΦθ0])
    _ = ((4 * p + 1) * K1 + 4) * (b + Φθ) := by ring
    _ = avmKd τ p C K3 * (b + Φθ) := by
        have e : avmKd τ p C K3 = (4 * p + 1) * K1 + 4 := by unfold avmKd; rw [hK1, hKcr]
        rw [e]

end Deriv

/-! ## Numerical facts on `𝐃^W` for large `N` -/

section Numerics

variable {N : ℕ}

/-- `κ/N ≤ Ψ²` on `S`, `κ = (3τ⁻¹ + 1)⁻²`. -/
private lemma avm_psi_sq_ge (hN : 1 ≤ N) {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) :
    ((3 * τ⁻¹ + 1) ^ 2)⁻¹ / N ≤ PsiW (specOf A) z ^ 2 := by
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := (avm_psi (a := specOf A) hN hzim).2.1
  have h2 := avm_im_ge hN hset hz
  refine le_trans ?_ h1
  rw [div_le_div_iff₀ hNp (by positivity)]
  calc ((3 * τ⁻¹ + 1) ^ 2)⁻¹ * (N * z.im) = (((3 * τ⁻¹ + 1) ^ 2)⁻¹ * z.im) * N := by ring
    _ ≤ (mW (specOf A) z).im * N := mul_le_mul_of_nonneg_right h2 hNp.le

/-- `Ψ ≤ 2 N^{−τ/2}` on `𝐃^W(τ, N)`. -/
private lemma avm_psi_le (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) {z : ℂ} (hz : z ∈ domW τ N)
    (a : Fin N → ℝ) : PsiW a z ≤ 2 * (N : ℝ) ^ (-τ / 2) := by
  obtain ⟨hzim, -, hηl, -⟩ := hz
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set x : ℝ := N * z.im with hx
  have hxτ : (N : ℝ) ^ τ ≤ x := by
    have : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [mul_comm, ← Real.rpow_add_one hNp.ne']; congr 1; ring
    rw [← this, hx]
    exact mul_le_mul_of_nonneg_left hηl hNp.le
  have hτ0 : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNp _
  have hx0 : 0 < x := lt_of_lt_of_le hτ0 hxτ
  have hm1 : (mW a z).im < 1 :=
    lt_of_le_of_lt (Complex.im_le_norm _) (norm_mW_lt_one hN a hzim)
  have hm0 : 0 < (mW a z).im := (mW_spec hN a hzim).1
  have hs : Real.sqrt (1 / x) ≤ (N : ℝ) ^ (-τ / 2) := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    rw [show -τ / 2 * ((2 : ℕ) : ℝ) = -τ by push_cast; ring, Real.rpow_neg hNp.le]
    rw [one_div]
    exact inv_anti₀ hτ0 hxτ
  have h1 : Real.sqrt ((mW a z).im / x) ≤ Real.sqrt (1 / x) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hm1.le hx0.le)
  have h2 : 1 / x ≤ Real.sqrt (1 / x) := by
    have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hNr hτ) hxτ
    have h01 : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx1
    have h00 : 0 ≤ 1 / x := by positivity
    rw [Real.le_sqrt h00 h00]
    nlinarith
  unfold PsiW
  linarith

/-- `K N^{εa − 1/2} ≤ 1` once `K ≤ N^{1/4}` and `εa ≤ 1/4`. -/
private lemma avm_r_le (hN : 1 ≤ N) {K εa : ℝ} (hεa : εa ≤ 1 / 4)
    (hKN : K ≤ (N : ℝ) ^ (1 / 4 : ℝ)) : K * (N : ℝ) ^ (εa - 1 / 2) ≤ 1 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) ^ (εa - 1 / 2) ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have h2 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hNp]; norm_num
  calc K * (N : ℝ) ^ (εa - 1 / 2) ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul hKN h1 (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
    _ = 1 := h2

/-- `N^{εa} Ψ ≤ 1` once `Ψ ≤ 2 N^{−τ/2}`, `εa ≤ τ/4` and `2 ≤ N^{τ/4}`. -/
private lemma avm_eΨ_le (hN : 1 ≤ N) {τ εa Ψ : ℝ} (hεa : εa ≤ τ / 4)
    (hΨ : Ψ ≤ 2 * (N : ℝ) ^ (-τ / 2)) (h2 : 2 ≤ (N : ℝ) ^ (τ / 4)) :
    (N : ℝ) ^ εa * Ψ ≤ 1 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h0 : 0 ≤ (N : ℝ) ^ εa := Real.rpow_nonneg hNp.le _
  have h1 : (N : ℝ) ^ εa * (N : ℝ) ^ (-τ / 2) ≤ (N : ℝ) ^ (-(τ / 4)) := by
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have h3 : (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (-(τ / 4)) = 1 := by
    rw [← Real.rpow_add hNp]; norm_num
  have h4 : 0 ≤ (N : ℝ) ^ (-(τ / 4)) := Real.rpow_nonneg hNp.le _
  calc (N : ℝ) ^ εa * Ψ ≤ (N : ℝ) ^ εa * (2 * (N : ℝ) ^ (-τ / 2)) :=
        mul_le_mul_of_nonneg_left hΨ h0
    _ = 2 * ((N : ℝ) ^ εa * (N : ℝ) ^ (-τ / 2)) := by ring
    _ ≤ 2 * (N : ℝ) ^ (-(τ / 4)) := by linarith
    _ ≤ (N : ℝ) ^ (τ / 4) * (N : ℝ) ^ (-(τ / 4)) := mul_le_mul_of_nonneg_right h2 h4
    _ = 1 := h3

/-- The remainder exponent: `K (N^{εa} Ψ)^p (N^{εa−1/2})^{4p+1−l} ≤ N^{l/2−2} Ψ^{2p}` for
`p = 2q ≥ 2`, `εa (5p + 1) ≤ 1/2`, `κ/N ≤ Ψ²` and `K κ^{−q} ≤ N`. -/
private lemma avm_rem_num (hN : 1 ≤ N) {K κ εa Ψ : ℝ} {p q : ℕ} (hpq : p = 2 * q)
    (hq : 1 ≤ q) (hκ : 0 < κ) (hΨ0 : 0 ≤ Ψ) (hΨκ : κ / N ≤ Ψ ^ 2)
    (hεa : 0 ≤ εa) (hεap : εa * (5 * p + 1) ≤ 1 / 2) (hKN : K * (κ ^ q)⁻¹ ≤ N) (l : ℕ)
    (hl : l ≤ 4 * p) :
    K * ((N : ℝ) ^ εa * Ψ) ^ p * ((N : ℝ) ^ (εa - 1 / 2)) ^ (4 * p - l + 1) ≤
      (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Ψ ^ (2 * p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set m : ℕ := 4 * p - l + 1 with hmdef
  have hm : (m : ℝ) = 4 * p - l + 1 := by
    rw [hmdef, Nat.cast_add, Nat.cast_sub hl]; push_cast; ring
  set a : ℝ := εa * p + (εa - 1 / 2) * m with ha
  set E : ℝ := (l : ℝ) / 2 - 2 - q - a with hE
  have hE1 : 1 ≤ E := by
    rw [hE, ha, hm]
    have hpq' : (p : ℝ) = 2 * q := by rw [hpq]; push_cast; ring
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hla : 0 ≤ εa * l := mul_nonneg hεa hl0
    nlinarith
  have hκq : 0 < κ ^ q := pow_pos hκ q
  have hKE : K ≤ κ ^ q * (N : ℝ) ^ E := by
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ E := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ E := Real.rpow_le_rpow_of_exponent_le hNr hE1
    have h2 : K * (κ ^ q)⁻¹ ≤ (N : ℝ) ^ E := hKN.trans h1
    rw [mul_inv_le_iff₀ hκq] at h2
    linarith
  have hpow1 : ((N : ℝ) ^ εa * Ψ) ^ p * ((N : ℝ) ^ (εa - 1 / 2)) ^ m = (N : ℝ) ^ a * Ψ ^ p := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ εa), ← Real.rpow_mul hNp.le,
      ← Real.rpow_natCast ((N : ℝ) ^ (εa - 1 / 2)), ← Real.rpow_mul hNp.le, ha,
      Real.rpow_add hNp]
    ring
  have hΨp : κ ^ q / (N : ℝ) ^ q ≤ Ψ ^ p := by
    rw [hpq, pow_mul, ← div_pow]
    exact pow_le_pow_left₀ (by positivity) hΨκ q
  have hEa : (N : ℝ) ^ E * (N : ℝ) ^ a = (N : ℝ) ^ ((l : ℝ) / 2 - 2) / (N : ℝ) ^ q := by
    rw [← Real.rpow_add hNp, hE, show (l : ℝ) / 2 - 2 - q - a + a = (l : ℝ) / 2 - 2 + -(q : ℝ) by
      ring, Real.rpow_add hNp, Real.rpow_neg hNp.le, Real.rpow_natCast]
    ring
  have hΨp0 : 0 ≤ Ψ ^ p := pow_nonneg hΨ0 p
  calc K * ((N : ℝ) ^ εa * Ψ) ^ p * ((N : ℝ) ^ (εa - 1 / 2)) ^ m
      = K * ((N : ℝ) ^ a * Ψ ^ p) := by rw [mul_assoc, hpow1]
    _ ≤ (κ ^ q * (N : ℝ) ^ E) * ((N : ℝ) ^ a * Ψ ^ p) :=
        mul_le_mul_of_nonneg_right hKE (by positivity)
    _ = (N : ℝ) ^ ((l : ℝ) / 2 - 2) * (κ ^ q / (N : ℝ) ^ q) * Ψ ^ p := by
        rw [show (κ ^ q * (N : ℝ) ^ E) * ((N : ℝ) ^ a * Ψ ^ p) =
          κ ^ q * ((N : ℝ) ^ E * (N : ℝ) ^ a) * Ψ ^ p by ring, hEa]
        ring
    _ ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Ψ ^ p * Ψ ^ p := by
        have := Real.rpow_nonneg hNp.le ((l : ℝ) / 2 - 2)
        gcongr
    _ = (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Ψ ^ (2 * p) := by rw [two_mul, pow_add]; ring

/-- `N^{−(10p+1)} ≤ N^{−2} Ψ^{2p}` once `κ/N ≤ Ψ²` and `κ⁻¹ ≤ N`. -/
private lemma avm_Γ0_num (hN : 1 ≤ N) {κ Ψ : ℝ} {p : ℕ} (hp : 1 ≤ p) (hκ : 0 < κ)
    (hΨκ : κ / N ≤ Ψ ^ 2) (hκN : κ⁻¹ ≤ N) :
    (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * Ψ ^ (2 * p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hκN' : (N : ℝ)⁻¹ ≤ κ := by rw [inv_le_comm₀ hNp hκ]; exact hκN
  have h1 : ((N : ℝ)⁻¹ / N) ^ p ≤ Ψ ^ (2 * p) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) (le_trans ?_ hΨκ) p
    exact div_le_div_of_nonneg_right hκN' hNp.le
  have h2 : ((N : ℝ)⁻¹ / N) ^ p = (N : ℝ) ^ (-(2 * (p : ℝ))) := by
    rw [Real.rpow_neg hNp.le, show (2 * (p : ℝ)) = ((2 * p : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, div_eq_mul_inv, ← mul_inv, ← pow_two, inv_pow, ← pow_mul]
  rw [h2] at h1
  have h3 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * (N : ℝ) ^ (-(2 * (p : ℝ))) := by
    rw [← Real.rpow_add hNp]
    refine Real.rpow_le_rpow_of_exponent_le hNr ?_
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    push_cast
    linarith
  exact h3.trans (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hNp.le _))

/-- The off-event term: `2 (4p+1)^p (4N)^{5p} (N² + 1) N^{−D} ≤ (N^{εa} Ψ²)^p` once
`D ≥ 6p + 3`, `κ/N ≤ Ψ²` and `4 (4p+1)^p 4^{5p} κ^{−p} ≤ N`. -/
private lemma avm_off_num (hN : 1 ≤ N) {κ Ψ εa Da : ℝ} {p : ℕ} (hκ : 0 < κ)
    (hΨκ : κ / N ≤ Ψ ^ 2) (hεa : 0 ≤ εa) (hDa : 6 * (p : ℝ) + 3 ≤ Da)
    (hKN : 4 * ((4 * p + 1 : ℕ) : ℝ) ^ p * 4 ^ (5 * p) * (κ ^ p)⁻¹ ≤ N) :
    2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) * (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da)) ≤
      ((N : ℝ) ^ εa * Ψ ^ 2) ^ p := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set Kh : ℝ := 4 * ((4 * p + 1 : ℕ) : ℝ) ^ p * 4 ^ (5 * p) with hKh
  have hKh0 : 0 ≤ Kh := by positivity
  have hκp : 0 < κ ^ p := pow_pos hκ p
  have hKh' : Kh ≤ κ ^ p * N := by
    rw [mul_inv_le_iff₀ hκp] at hKN; linarith
  have hR : κ ^ p / (N : ℝ) ^ p ≤ ((N : ℝ) ^ εa * Ψ ^ 2) ^ p := by
    rw [← div_pow]
    refine pow_le_pow_left₀ (by positivity) (hΨκ.trans ?_) p
    exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow hNr hεa)
  have hD : (N : ℝ) ^ (-Da) ≤ ((N : ℝ) ^ (6 * p + 3))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hNp.le]
    refine Real.rpow_le_rpow_of_exponent_le hNr ?_
    push_cast; linarith
  have hN2 : (N : ℝ) ^ 2 + 1 ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
  refine le_trans ?_ hR
  have hNpow : 0 < (N : ℝ) ^ (6 * p + 3) := by positivity
  calc 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) * (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da))
      ≤ 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) *
        ((2 * (N : ℝ) ^ 2) * ((N : ℝ) ^ (6 * p + 3))⁻¹) := by
        gcongr
    _ = Kh * ((N : ℝ) ^ (5 * p) * (N : ℝ) ^ 2 * ((N : ℝ) ^ (6 * p + 3))⁻¹) := by
        rw [hKh, mul_pow]; ring
    _ = Kh / N / (N : ℝ) ^ p := by
        rw [show 6 * p + 3 = 5 * p + 2 + p + 1 by ring]
        field_simp
        ring
    _ ≤ κ ^ p / (N : ℝ) ^ p := by
        gcongr
        rw [div_le_iff₀ hNp]; linarith

end Numerics

/-! ## The moment bound by Grönwall over `θ` -/

section Core

variable {N : ℕ}

/-- Grönwall over `θ` at a fixed `N`: `E F̃^p(W) ≤ (2 e^K − 1) (b + G₀)` from
`E F̃^p(W^Gauss) ≤ G₀` and the derivative bound. -/
private lemma avm_core_fixed (hN : 2 ≤ N) {τ c₀ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {S : Set ℂ} (hset : WigSetting τ N A S) {z : ℂ} (hz : z ∈ S) (hηN : z.im⁻¹ ≤ N)
    {C : ℕ → ℝ} {p : ℕ} (hp : Even p) (hp2 : 2 ≤ p) {εa Da r δ K3 : ℝ} (hεa : 0 ≤ εa)
    (hK3 : 0 ≤ K3) (heΨ : (N : ℝ) ^ εa * PsiW (specOf A) z ≤ 1)
    (hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4) (hr2 : 12 * r * avmC1 τ ≤ 1)
    (hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ Da - 3)
    (hrem : ∀ l ≤ 4 * p, avmKRg τ p * ((N : ℝ) ^ εa * PsiW (specOf A) z) ^ p *
      r ^ (4 * p - l + 1) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p))
    (hΓ0 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2) * PsiW (specOf A) z ^ (2 * p))
    (hKM : avmKM p (momMaxW C) ≤ N)
    (hoff : 2 * ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) *
      (((N : ℝ) ^ 2 + 1) * (N : ℝ) ^ (-Da)) ≤ ((N : ℝ) ^ εa * PsiW (specOf A) z ^ 2) ^ p)
    (heδ : (N : ℝ) ^ εa ≤ (N : ℝ) ^ δ) (Q : ModelClassW N)
    (hAL : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (Y : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N Y → Q Ω' Y →
      AnisotropicLawWAt N εa Da A Y {z})
    (hmk : ∀ {Ω' : Type} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (y : Ω' → ℝ), (∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
        ∫ ω, |Real.sqrt N * y ω| ^ q ≤ momMaxW C q) →
      HighProbAt N Da {ω | |y ω| ≤ r})
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (W : Ω → Matrix (Fin N) (Fin N) ℝ) (hW : WigClassEntries (momMaxW C) N W)
    (hQ1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      Q (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper)
    (hQ2 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ α : UpperIdx N,
      Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α (entryLawW W α))) ofUpper ∧
      Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α (goeLaw N α))) ofUpper)
    (h3 : (∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0) ∨
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ s : UpperIdx N → ℂ, (∀ α, ‖s α‖ ≤ 1) →
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α *
          ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
            fCoeff p (avgCoeffW A (ofUpper ω) z α.1.1 α.1.2) 3‖ ≤
          K3 * (((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p +
            ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p +
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              FtW A (ofUpper ω) z ^ p)) :
    ∫ ω, FtW A (W ω) z ^ p ≤ (2 * Real.exp (avmKd τ p C K3) - 1) *
      ((((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) +
        ∫ ω, FtW A (goeW N ω) z ^ p) := by
  have hN1 : 1 ≤ N := by omega
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  have hτ := hset.pos
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := avm_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := avm_entryLawW_prob hW.measurable
  set K' := avmKd τ p C K3 with hK'
  have hK'0 : 0 ≤ K' := avmKd_nonneg hτ p C hK3
  set b : ℝ := ((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p +
    ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p with hb
  have hb0 : 0 ≤ b := by
    have : 0 ≤ PsiW (specOf A) z :=
      le_trans (by positivity) (avm_psi (a := specOf A) hN1 hzim).1
    positivity
  set G0 : ℝ := ∫ ω, FtW A (goeW N ω) z ^ p with hG0
  have hG00 : 0 ≤ G0 := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p
  set F : (UpperIdx N → ℝ) → ℝ := fun x => FtW A (ofUpper x) z ^ p with hF
  have hFm : Measurable F := ((avm_measurable_Ft A z).comp avm_measurable_ofUpper).pow_const p
  have hFb : ∀ x, ‖F x‖ ≤ (z.im⁻¹ + 1) ^ p := fun x => by
    have h0 : 0 ≤ FtW A (ofUpper x) z := norm_nonneg _
    rw [Real.norm_of_nonneg (pow_nonneg h0 p)]
    exact pow_le_pow_left₀ h0 (avm_FtW_le hN1 hset.symmA (avm_ofUpper_symm x) hzim) p
  have hint : ∀ u, Integrable F (vertexLaw (goeLaw N) (entryLawW W) u) := by
    intro u
    have : ∀ α, IsProbabilityMeasure (if u α then entryLawW W α else goeLaw N α) := by
      intro α; split <;> infer_instance
    have : IsProbabilityMeasure (vertexLaw (goeLaw N) (entryLawW W) u) := by
      unfold vertexLaw; infer_instance
    exact Integrable.of_bound hFm.aestronglyMeasurable _ (ae_of_all _ hFb)
  set Φ := interpPoly (goeLaw N) (entryLawW W) F with hΦ
  set Φ' : ℝ → ℝ := fun θ => ∑ α : UpperIdx N,
      ((∫ x, F x ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α))) -
        ∫ x, F x ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α))) with hΦ'
  have hΦeq : ∀ θ ∈ Set.Icc (0 : ℝ) 1, Φ θ = ∫ x, F x ∂(interpLaw θ (goeLaw N) (entryLawW W)) :=
    fun θ hθ => (integral_interpLaw_eq_interpPoly hθ.1 hθ.2 hFm hint).symm
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ (Φ' θ) θ :=
    fun θ hθ => hasDerivAt_interpPoly hθ.1 hθ.2 hFm hint
  -- `Φ(0) ≤ b + G₀`
  have h0 : Φ 0 ≤ b + G0 := by
    rw [hΦeq 0 ⟨le_rfl, zero_le_one⟩, avm_interpLaw_zero]
    have hgl : goeLaw N = entryLawW (goeW N) := funext fun α => (avm_entryLawW_goeW N α).symm
    rw [hgl, avm_integral_pi_entryLaw (F := fun M => FtW A M z ^ p)
      ((isGOE_goeW N).classEntries hN1) hFm]
    linarith
  -- Grönwall
  have hgr := gronwall_affine (Φ := Φ) (Φ' := Φ') (K := K') (a := b + G0) hK'0
    (by linarith)
    (fun θ hθ => (hderiv θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ => hderiv θ ⟨hθ.1, hθ.2.le⟩)
    (fun θ hθ => by
      have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1, hθ.2.le⟩
      have h := avm_deriv_bound hN hset hz hηN hp hp2 hεa hK3 heΨ hr1 hr2 hD hrem hΓ0 hKM hoff
        heδ Q hAL hmk W hW hQ1 hQ2 h3 θ hθ'
      rw [hΦeq θ hθ']
      refine (le_abs_self _).trans (h.trans ?_)
      have hI : 0 ≤ ∫ x, FtW A (ofUpper x) z ^ p ∂(interpLaw θ (goeLaw N) (entryLawW W)) :=
        integral_nonneg fun x => pow_nonneg (norm_nonneg _) p
      exact mul_le_mul_of_nonneg_left (by linarith) hK'0)
    h0
  -- `Φ(1) = E F̃^p(W)`
  have h1 : ∫ ω, FtW A (W ω) z ^ p = Φ 1 := by
    rw [hΦeq 1 ⟨zero_le_one, le_rfl⟩, avm_interpLaw_one]
    exact (avm_integral_pi_entryLaw (F := fun M => FtW A M z ^ p) hW hFm).symm
  rw [h1]
  exact hgr

end Core

/-! ## The moment bound for every matrix of the class -/

section Moment

/-- `WigClassEntries C ⊆ WigClassEntries (momMaxW C)`. -/
private lemma avm_class_mono {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) :
    WigClassEntries (momMaxW C) N W :=
  ⟨hW.measurable, hW.symm, hW.indep, hW.mean, hW.var_off, hW.var_diag_ge, hW.var_diag_le,
    hW.integrable_moment, fun p i j => (hW.moment p i j).trans (le_max_left _ _)⟩

/-- Lemma 12.8 integrated over `θ` (the averaged comparison): for `p` even, `εa ≤ δ/4`,
`εa ≤ τ/4`, `εa (5p + 1) ≤ 1/2` and `D_a ≥ dPrev p`, if the anisotropic law at `(εa, D_a)` holds
for every matrix of the class with moments `momMaxW C` under (a) or (b), then
`E F̃^p(W) ≤ K ((N^δ Ψ²)^p + (N^{−c₀/2} (Nη)⁻¹)^p + E F̃^p(W^Gauss))` for every `W` of the class
under (a) or (b). -/
private lemma avm_moment (τ c₀ : ℝ) (C : ℕ → ℝ) (p : ℕ) (δ εa Da : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc₀ : 0 < c₀) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hεa : 0 < εa)
    (hεaδ : εa ≤ δ / 4) (hεaτ : εa ≤ τ / 4) (hεap : εa * (5 * p + 1) ≤ 1 / 2)
    (hDa : dPrev p ≤ Da) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WigSetting τ N A S →
      (∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
        (Y : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N Y →
        ((∀ i j, ∫ ω, Y ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
        AnisotropicLawWAt N εa Da A Y S) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W →
        ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
        ∀ z ∈ S, ∫ ω, FtW A (W ω) z ^ p ≤
          Kc * ((((N : ℝ) ^ δ * PsiW (specOf A) z ^ 2) ^ p +
            ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) + ∫ ω, FtW A (goeW N ω) z ^ p) := by
  obtain ⟨K3, hK3, N3, h3c⟩ := wig_avg_coeff τ c₀ (momMaxW C) p δ εa Da hτ hτ1 hc₀ hp hp2 hδ
    hεa hεaδ hDa
  obtain ⟨Nm, hm⟩ := avm_markov (momMaxW C) εa Da hεa
  obtain ⟨q, hq⟩ := hp
  have hpq : p = 2 * q := by omega
  have hq1 : 1 ≤ q := by omega
  set κ : ℝ := ((3 * τ⁻¹ + 1) ^ 2)⁻¹ with hκdef
  have hκ : 0 < κ := by
    have : 0 < τ⁻¹ := inv_pos.2 hτ
    positivity
  have hT0 : 0 < τ⁻¹ + 1 := by have := inv_pos.2 hτ; linarith
  have hc1 := avmC1_pos hτ
  refine ⟨2 * Real.exp (avmKd τ p C K3), by positivity,
    max (max (max N3 Nm) (max 2 ⌈(2 : ℝ) ^ (τ / 4)⁻¹⌉₊))
      (max (max ⌈(8 * (τ⁻¹ + 1)) ^ (1 / 4 : ℝ)⁻¹⌉₊ ⌈(12 * avmC1 τ) ^ (1 / 4 : ℝ)⁻¹⌉₊)
        (max (max ⌈avmKRg τ p * (κ ^ q)⁻¹⌉₊ ⌈κ⁻¹⌉₊)
          (max ⌈avmKM p (momMaxW C)⌉₊ ⌈4 * ((4 * p + 1 : ℕ) : ℝ) ^ p * 4 ^ (5 * p) *
            (κ ^ p)⁻¹⌉₊))), ?_⟩
  intro N hN A S hset hALc Ω _ _ W hW hcase z hz
  have hN3 : N3 ≤ N := by omega
  have hNm : Nm ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hzD : z ∈ domW τ N := hset.domain.1 hz
  have hzim : 0 < z.im := hzD.1
  have hηN : z.im⁻¹ ≤ N := avm_im_inv_le hN1 hτ hzD
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) (avm_psi (a := specOf A) hN1 hzim).1
  have hceil : ∀ x : ℝ, ⌈x⌉₊ ≤ N → x ≤ N := fun x h =>
    (Nat.le_ceil _).trans (by exact_mod_cast h)
  have h2τ : 2 ≤ (N : ℝ) ^ (τ / 4) := avm_le_rpow (by norm_num) (by positivity) (by omega)
  have heΨ : (N : ℝ) ^ εa * Ψ ≤ 1 :=
    avm_eΨ_le hN1 hεaτ (avm_psi_le hN1 hτ.le hzD (specOf A)) h2τ
  have hεa4 : εa ≤ 1 / 4 := by linarith
  set r : ℝ := (N : ℝ) ^ (εa - 1 / 2) with hr
  have hr1 : 2 * r * (τ⁻¹ + 1) ≤ 1 / 4 := by
    have h := avm_r_le hN1 hεa4 (avm_le_rpow (by positivity) (by norm_num) (by omega) :
      8 * (τ⁻¹ + 1) ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    rw [← hr] at h
    linarith
  have hr2 : 12 * r * avmC1 τ ≤ 1 := by
    have h := avm_r_le hN1 hεa4 (avm_le_rpow (by positivity) (by norm_num) (by omega) :
      12 * avmC1 τ ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    rw [← hr] at h
    linarith
  have hDp : (100 : ℝ) * ((p : ℝ) + 1) ^ 2 ≤ Da := hDa
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ Da - 3 := by push_cast; nlinarith
  have hD6 : 6 * (p : ℝ) + 3 ≤ Da := by nlinarith
  have hΨκ : κ / N ≤ Ψ ^ 2 := avm_psi_sq_ge hN1 hset hz
  have hrem : ∀ l ≤ 4 * p, avmKRg τ p * ((N : ℝ) ^ εa * Ψ) ^ p * r ^ (4 * p - l + 1) ≤
      (N : ℝ) ^ ((l : ℝ) / 2 - 2) * Ψ ^ (2 * p) := fun l hl =>
    avm_rem_num hN1 hpq hq1 hκ hΨ0 hΨκ hεa.le hεap (hceil _ (by omega)) l hl
  have hΓ0 := avm_Γ0_num (N := N) (p := p) hN1 (by omega) hκ hΨκ (hceil _ (by omega))
  have hKM : avmKM p (momMaxW C) ≤ N := hceil _ (by omega)
  have hoff := avm_off_num (εa := εa) hN1 hκ hΨκ hεa.le hD6 (hceil _ (by omega))
  have heδ : (N : ℝ) ^ εa ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hmk := fun {Ω' : Type} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')] =>
    hm N hNm (Ω := Ω')
  have hWc := avm_class_mono hW
  set Q : ModelClassW N := fun Ω' _ Y =>
    (∀ i j, ∫ ω, Y ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S with hQ
  have hAL : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (Y : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N Y → Q Ω' Y →
      AnisotropicLawWAt N εa Da A Y {z} := by
    intro Ω' _ _ Y hY hQY z' hz'
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    exact hALc Ω' Y hY hQY z' hz
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := avm_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := avm_entryLawW_prob hW.measurable
  have hcore : ∀ (h3 : (∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0) ∨
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ s : UpperIdx N → ℂ, (∀ α, ‖s α‖ ≤ 1) →
        (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α *
          ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
            fCoeff p (avgCoeffW A (ofUpper ω) z α.1.1 α.1.2) 3‖ ≤
          K3 * (((N : ℝ) ^ δ * Ψ ^ 2) ^ p + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p +
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              FtW A (ofUpper ω) z ^ p)),
      (∀ θ ∈ Set.Icc (0 : ℝ) 1,
        Q (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ α : UpperIdx N,
        Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α (entryLawW W α))) ofUpper ∧
        Q (AvmPi N (avmPairLaw θ (goeLaw N) (entryLawW W) α (goeLaw N α))) ofUpper) →
      ∫ ω, FtW A (W ω) z ^ p ≤
        2 * Real.exp (avmKd τ p C K3) * ((((N : ℝ) ^ δ * Ψ ^ 2) ^ p +
          ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) + ∫ ω, FtW A (goeW N ω) z ^ p) := by
    intro h3 hQ1 hQ2
    have h := avm_core_fixed hN2 hset hz hηN ⟨q, hq⟩ hp2 hεa.le hK3 heΨ hr1 hr2 hD hrem hΓ0 hKM
      hoff heδ Q hAL hmk W hWc hQ1 hQ2 h3
    refine h.trans ?_
    have hX : 0 ≤ (((N : ℝ) ^ δ * Ψ ^ 2) ^ p + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) +
        ∫ ω, FtW A (goeW N ω) z ^ p := by
      have : 0 ≤ ∫ ω, FtW A (goeW N ω) z ^ p :=
        integral_nonneg fun ω => pow_nonneg (norm_nonneg _) p
      have : 0 ≤ ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p := by positivity
      have : 0 ≤ ((N : ℝ) ^ δ * Ψ ^ 2) ^ p := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right (by linarith) hX
  rcases hcase with h3W | hPs
  · refine hcore (Or.inl fun α => avm_entryLawW_third hWc.measurable h3W α)
      (fun θ hθ => Or.inl (zeroThirdW_interp hN1 hWc h3W hθ.1 hθ.2))
      (fun θ hθ α => ⟨Or.inl (avm_zeroThird_pair hN1 hWc h3W hθ.1 hθ.2 α (entryLawW W α)
          (avm_entryLawW_third hWc.measurable h3W α)),
        Or.inl (avm_zeroThird_pair hN1 hWc h3W hθ.1 hθ.2 α (goeLaw N α)
          (avm_integral_cube_gaussianReal _))⟩)
  · refine hcore (Or.inr fun θ hθ s hs => ?_) (fun θ _ => Or.inr hPs)
      (fun θ _ α => ⟨Or.inr hPs, Or.inr hPs⟩)
    have : ∀ β : UpperIdx N, IsProbabilityMeasure (mixMeasure θ (goeLaw N β) (entryLawW W β)) :=
      fun β => isProbabilityMeasure_mixMeasure θ _ _
    have hIP : IsProbabilityMeasure (interpLaw θ (goeLaw N) (entryLawW W)) := by
      unfold interpLaw
      infer_instance
    have : IsProbabilityMeasure
        (ℙ : Measure (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W))) := hIP
    have hWθ : WigClassEntries (momMaxW C)
        (Ω := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) N ofUpper :=
      avm_class_interp hN1 hWc hθ.1 hθ.2
    have h := h3c N hN3 A S hset (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper
      hWθ z hz (hAL (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ
        (Or.inr hPs)) s 3 hs
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) (fun _ => hPs)
    simpa only [Nat.cast_ofNat] using h

end Moment

/-! ## Monotonicity, the empty domain, and `Ψ² ≤ 4 (Nη)⁻¹` -/

section Final

/-- Monotonicity of `DomAt` in `ε` and `D`. -/
private lemma avm_dom_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N) {ε ε' D D' : ℝ}
    {ξ ζ : Ω → ℝ} (hζ : ∀ ω, 0 ≤ ζ ω) (hε : ε ≤ ε') (hD : D' ≤ D) (h : DomAt N ε D ξ ζ) :
    DomAt N ε' D' ξ ζ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold DomAt at h ⊢
  refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 hε) (hζ ω)) hω

/-- `𝐃^W(τ, N)` is empty for `τ > 1`. -/
private lemma avm_domW_empty {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ1 : 1 < τ) {z : ℂ} :
    z ∉ domW τ N := by
  rintro ⟨hz0, -, hzl, hzu⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) := Real.one_le_rpow hNr (by linarith)
  have h2 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hτ1
  linarith

/-- `1 ≤ N η` on `𝐃^W(τ, N)` for `τ ≥ 0`. -/
private lemma avm_one_le_Neta {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) {z : ℂ}
    (hz : z ∈ domW τ N) : 1 ≤ (N : ℝ) * z.im := by
  obtain ⟨-, -, hηl, -⟩ := hz
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
    rw [mul_comm, ← Real.rpow_add_one hNp.ne']; congr 1; ring
  calc (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hNr hτ
    _ = (N : ℝ) * (N : ℝ) ^ (-1 + τ) := h1.symm
    _ ≤ (N : ℝ) * z.im := mul_le_mul_of_nonneg_left hηl hNp.le

/-- `Ψ² ≤ 4 (Nη)⁻¹` when `Nη ≥ 1`. -/
private lemma avm_psi_sq_le {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im)
    (hNη : 1 ≤ (N : ℝ) * z.im) : PsiW a z ^ 2 ≤ 4 * (1 / (N * z.im)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < (N : ℝ) * z.im := by linarith
  have hm1 : (mW a z).im < 1 :=
    lt_of_le_of_lt (Complex.im_le_norm _) (norm_mW_lt_one hN a hz)
  have hm0 : 0 < (mW a z).im := (mW_spec hN a hz).1
  set u := Real.sqrt ((mW a z).im / (N * z.im)) with hu
  set v : ℝ := 1 / (N * z.im) with hv
  have hu2 : u ^ 2 = (mW a z).im / (N * z.im) := Real.sq_sqrt (by positivity)
  have hu2' : u ^ 2 ≤ v := by
    rw [hu2, hv]; exact div_le_div_of_nonneg_right hm1.le hx0.le
  have hv1 : v ≤ 1 := by rw [hv, div_le_one hx0]; exact hNη
  have hv0 : 0 ≤ v := by positivity
  have hv2 : v ^ 2 ≤ v := by nlinarith
  unfold PsiW
  rw [← hu, ← hv]
  nlinarith [sq_nonneg (u - v)]

private lemma avm_aux_pow {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    (2 / a ^ 2) ^ p * (a / b) ^ (2 * p) = (2 / b ^ 2) ^ p := by
  rw [pow_mul, ← mul_pow]
  congr 1
  field_simp

end Final

/-- Theorem 12.2 (ii), strong form: the GOE averaged error `Φ` is transferred with the extra error
`Ψ² + N^{−c₀/2}(Nη)⁻¹`, for every `W` of the class. -/
private theorem avm_avg_phi (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (Φ : ℂ → ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ → WigClassEntries C N W → SpectralDomainW τ N S →
      StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      (∀ z ∈ S, 0 ≤ Φ z ∧ Φ z ≤ 1 / (N * z.im)) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedPhiLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S Φ →
      AveragedPhiLawWAt N ε D A W S
        (fun z => Φ z + PsiW (specOf A) z ^ 2 + (N : ℝ) ^ (-c₀ / 2) / (N * z.im)) := by
  by_cases hτ1 : τ ≤ 1
  swap
  · push Not at hτ1
    refine ⟨1, 0, one_pos, 1, ?_⟩
    intro N hN Ω _ _ A W S Φ _ _ _ hS _ _ _ _ _ z hz
    exact absurd (hS.1 hz) (avm_domW_empty hN hτ1)
  -- the parameters
  set p : ℕ := 2 * (⌈2 * max D 0 / ε⌉₊ + 1) with hpdef
  have hpE : Even p := ⟨⌈2 * max D 0 / ε⌉₊ + 1, by omega⟩
  have hp2 : 2 ≤ p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set εa : ℝ := min (δ / 4) (min (τ / 4) (1 / (2 * (5 * p + 1)))) with hεadef
  have hεa : 0 < εa := by
    refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεaδ : εa ≤ δ / 4 := min_le_left _ _
  have hεaτ : εa ≤ τ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεap : εa * (5 * p + 1) ≤ 1 / 2 := by
    have h1 : εa ≤ 1 / (2 * (5 * p + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : (0 : ℝ) < 5 * p + 1 := by positivity
    calc εa * (5 * p + 1) ≤ 1 / (2 * (5 * p + 1)) * (5 * p + 1) :=
          mul_le_mul_of_nonneg_right h1 h2.le
      _ = 1 / 2 := by field_simp
  set Da : ℝ := dPrev p with hDadef
  obtain ⟨ε₂, D₂, hε₂, N₂, h2⟩ := general_wig_aniso_class τ c₀ (momMaxW C) εa Da hτ hc₀ hεa
  obtain ⟨Kc, hKc, N₃, h3⟩ := avm_moment τ c₀ C p δ εa Da hτ hτ1 hc₀ hpE hp2 hδ hεa hεaδ hεaτ
    hεap le_rfl
  have hpε : 0 < (p : ℝ) * ε / 4 := by positivity
  refine ⟨min ε₂ (ε / 4), max D₂ (3 * p + 2), lt_min hε₂ (by positivity),
    max (max N₂ N₃) (max 2 (max ⌈(2 / τ ^ 2) ^ p⌉₊ ⌈(4 * Kc) ^ ((p : ℝ) * ε / 4)⁻¹⌉₊)), ?_⟩
  intro N hN Ω _ _ A W S Φ hA hnA hW hS hb hcase hΦ hEnt hAvg z hz
  have hN₂ : N₂ ≤ N := by omega
  have hN₃ : N₃ ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hset : WigSetting τ N A S := ⟨hτ, hτ1, hA, hnA, hS, hb⟩
  have hzD : z ∈ domW τ N := hS.1 hz
  have hzim : 0 < z.im := hzD.1
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨτ : τ / N ≤ Ψ := avm_psi_ge hN1 hτ _ hzD
  have hΨpos : 0 < Ψ := lt_of_lt_of_le (by positivity) hΨτ
  obtain ⟨hΦ0, -⟩ := hΦ z hz
  -- the anisotropic law for the class
  have hEnt2 : EntrywiseLawWAt N ε₂ D₂ (diagonal (specOf A)) (goeW N) S := by
    intro z' hz' s t
    refine avm_dom_mono hN1 (fun _ => ?_) (min_le_left _ _) (le_max_left _ _) (hEnt z' hz' s t)
    exact le_trans (by positivity) (avm_psi_ge hN1 hτ _ (hS.1 hz'))
  have hALc : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
      (Y : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N Y →
      ((∀ i j, ∫ ω, Y ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      AnisotropicLawWAt N εa Da A Y S :=
    fun Ω' _ _ Y hY hcY => h2 N hN₂ A Y S hA hnA hY hS hb hcY hEnt2
  have hmom := h3 N hN₃ A S hset hALc Ω W hW hcase z hz
  -- the Gaussian start
  have hG := goe_avg_rotate hA (isGOE_goeW N) hAvg z hz
  have hηN : z.im⁻¹ ≤ N := avm_im_inv_le hN1 hτ hzD
  have hGm : Measurable fun ω => FtW A (goeW N ω) z :=
    (avm_measurable_Ft A z).comp (avm_measurable_goeW N)
  have hGs := avm_moment_of_dom (ξ := fun ω => FtW A (goeW N ω) z) (ε := min ε₂ (ε / 4))
    (D := max D₂ (3 * p + 2)) (ζ := Φ z) (M := z.im⁻¹ + 1) p hGm (fun ω => norm_nonneg _)
    (fun ω => avm_FtW_le hN1 hA ((isGOE_goeW N).symm ω) hzim) hΦ0 (by positivity) hN1 hG
  have htail : (z.im⁻¹ + 1) ^ p * (N : ℝ) ^ (-max D₂ (3 * p + 2)) ≤ Ψ ^ (2 * p) := by
    have hM : z.im⁻¹ + 1 ≤ 2 * N := by linarith
    have h1 : (z.im⁻¹ + 1) ^ p ≤ (2 * N) ^ p := pow_le_pow_left₀ (by positivity) hM p
    have h2' : (N : ℝ) ^ (-max D₂ (3 * p + 2)) ≤ ((N : ℝ) ^ (3 * p + 2))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hNp.le]
      refine Real.rpow_le_rpow_of_exponent_le hNr ?_
      push_cast
      linarith [le_max_right D₂ (3 * (p : ℝ) + 2)]
    have h3' : (τ / N) ^ (2 * p) ≤ Ψ ^ (2 * p) := pow_le_pow_left₀ (by positivity) hΨτ _
    have h2τ : (2 / τ ^ 2) ^ p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (by omega :
      ⌈(2 / τ ^ 2) ^ p⌉₊ ≤ N))
    refine le_trans ?_ h3'
    have hNpow : (0 : ℝ) < (N : ℝ) ^ (3 * p + 2) := by positivity
    calc (z.im⁻¹ + 1) ^ p * (N : ℝ) ^ (-max D₂ (3 * p + 2))
        ≤ (2 * N) ^ p * ((N : ℝ) ^ (3 * p + 2))⁻¹ :=
          mul_le_mul h1 h2' (Real.rpow_nonneg hNp.le _) (by positivity)
      _ = (2 / (N : ℝ) ^ 2) ^ p / (N : ℝ) ^ 2 := by
          rw [div_pow, mul_pow, ← pow_mul, show 3 * p + 2 = p + 2 * p + 2 by ring, pow_add,
            pow_add]
          field_simp
      _ = (2 / τ ^ 2) ^ p * (τ / N) ^ (2 * p) / (N : ℝ) ^ 2 := by
          rw [avm_aux_pow hτ.ne' hNp.ne' p]
      _ ≤ N * (τ / N) ^ (2 * p) / (N : ℝ) ^ 2 := by gcongr
      _ = (τ / N) ^ (2 * p) / N := by field_simp
      _ ≤ (τ / N) ^ (2 * p) := div_le_self (by positivity) hNr
  -- the moment bound
  set Φ' : ℝ := Φ z + Ψ ^ 2 + (N : ℝ) ^ (-c₀ / 2) / (N * z.im) with hΦ'
  have hcterm : 0 ≤ (N : ℝ) ^ (-c₀ / 2) / (N * z.im) := by positivity
  have hΦ'pos : 0 < Φ' := by have := pow_pos hΨpos 2; linarith
  have hN4 : (N : ℝ) ^ (ε / 4) * Φ' ≥ Φ' := le_mul_of_one_le_left hΦ'pos.le
    (Real.one_le_rpow hNr (by positivity))
  set X : ℝ := (N : ℝ) ^ (ε / 4) * Φ' with hX
  have hX0 : 0 ≤ X := by positivity
  have t1 : ((N : ℝ) ^ δ * Ψ ^ 2) ^ p ≤ X ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hNp.le _)
  have t2 : ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p ≤ X ^ p :=
    pow_le_pow_left₀ hcterm (by have := pow_nonneg hΨpos.le 2; linarith) p
  have t3 : ((N : ℝ) ^ min ε₂ (ε / 4) * Φ z) ^ p ≤ X ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    have hNe : (N : ℝ) ^ min ε₂ (ε / 4) ≤ (N : ℝ) ^ (ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hNr (min_le_right _ _)
    have : Φ z ≤ Φ' := by have := pow_nonneg hΨpos.le 2; linarith
    exact mul_le_mul hNe this hΦ0 (Real.rpow_nonneg hNp.le _)
  have t4 : Ψ ^ (2 * p) ≤ X ^ p := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) p
  have hK4 : 4 * Kc ≤ (N : ℝ) ^ ((p : ℝ) * ε / 4) :=
    avm_le_rpow (by positivity) hpε (by omega)
  have hmom' : ∫ ω, FtW A (W ω) z ^ p ≤ ((N : ℝ) ^ (ε / 2) * Φ') ^ p := by
    refine hmom.trans ?_
    have hG' : ∫ ω, FtW A (goeW N ω) z ^ p ≤ X ^ p + X ^ p := by
      refine hGs.trans ?_
      linarith
    have hsum : (((N : ℝ) ^ δ * Ψ ^ 2) ^ p + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) +
        ∫ ω, FtW A (goeW N ω) z ^ p ≤ 4 * X ^ p := by linarith
    have hXp : ((N : ℝ) ^ (ε / 2) * Φ') ^ p = (N : ℝ) ^ ((p : ℝ) * ε / 4) * X ^ p := by
      rw [hX, mul_pow, mul_pow, ← mul_assoc, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 2)),
        ← Real.rpow_natCast ((N : ℝ) ^ (ε / 4)), ← Real.rpow_mul hNp.le,
        ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
      congr 2
      ring
    rw [hXp]
    calc Kc * ((((N : ℝ) ^ δ * Ψ ^ 2) ^ p + ((N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ^ p) +
          ∫ ω, FtW A (goeW N ω) z ^ p) ≤ Kc * (4 * X ^ p) :=
          mul_le_mul_of_nonneg_left hsum hKc
      _ = 4 * Kc * X ^ p := by ring
      _ ≤ (N : ℝ) ^ ((p : ℝ) * ε / 4) * X ^ p :=
          mul_le_mul_of_nonneg_right hK4 (pow_nonneg hX0 p)
  -- Markov
  have hWm : Measurable W := measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b =>
    hW.measurable a b
  have hint : Integrable fun ω => FtW A (W ω) z ^ p :=
    Integrable.of_bound (((avm_measurable_Ft A z).comp hWm).pow_const p).aestronglyMeasurable
      ((z.im⁻¹ + 1) ^ p) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (show 0 ≤ FtW A (W ω) z from norm_nonneg _) p)]
        exact pow_le_pow_left₀ (norm_nonneg _) (avm_FtW_le hN1 hA (hW.symm ω) hzim) p)
  have hDp : D ≤ (ε - ε / 2) * p := by
    have h1 : 2 * max D 0 / ε ≤ (⌈2 * max D 0 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (p : ℝ) = 2 * ((⌈2 * max D 0 / ε⌉₊ : ℝ) + 1) := by rw [hpdef]; push_cast; ring
    have h3 : (ε - ε / 2) * (2 * (2 * max D 0 / ε)) = 2 * max D 0 := by field_simp; ring
    have h4 : (ε - ε / 2) * (2 * (2 * max D 0 / ε)) ≤ (ε - ε / 2) * p := by
      rw [h2]
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h5 := le_max_left D 0
    have h6 := le_max_right D 0
    linarith
  exact DomAt.of_moment (ε := ε / 2) (ε' := ε) p hN1 hDp (fun ω => norm_nonneg _) hΦ'pos hint
    hmom'

/-- Theorem 12.2 (ii) (`lem:general Wig`) at fixed `N`. -/
theorem general_wig_avg (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ),
      WignerModel τ C N A W → SpectralDomainW τ N S → StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedLawWAt N ε D A W S := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ := avm_avg_phi τ c₀ C (ε / 2) D hτ hc₀ (half_pos hε)
  refine ⟨ε₁, D₁, hε₁, max N₀ (max 1 ⌈(6 : ℝ) ^ (ε / 2)⁻¹⌉₊), ?_⟩
  intro N hN Ω _ _ A W S hm hS hb hcase hEnt hAvg z hz
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  by_cases hτ1 : τ ≤ 1
  swap
  · exact absurd (hS.1 hz) (avm_domW_empty hN1 (by linarith))
  have hzD := hS.1 hz
  have hzim : 0 < z.im := hzD.1
  have hphi := h N (by omega) A W S (fun z => 1 / (N * z.im)) hm.symmA hm.normA
    hm.entries.toClass hS hb hcase
    (fun z' hz' => ⟨by have := (hS.1 hz').1; positivity, le_rfl⟩) hEnt hAvg z hz
  have hNη := avm_one_le_Neta hN1 hτ.le hzD
  have hΨ := avm_psi_sq_le hN1 (specOf A) hzim hNη
  have hc : (N : ℝ) ^ (-c₀ / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  have h6 : (6 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := avm_le_rpow (by norm_num) (by positivity) (by omega)
  have hv0 : 0 ≤ 1 / ((N : ℝ) * z.im) := by positivity
  have hbound : (N : ℝ) ^ (ε / 2) * (1 / (N * z.im) + PsiW (specOf A) z ^ 2 +
      (N : ℝ) ^ (-c₀ / 2) / (N * z.im)) ≤ (N : ℝ) ^ ε * (1 / (N * z.im)) := by
    have h1 : (N : ℝ) ^ (-c₀ / 2) / (N * z.im) ≤ 1 / (N * z.im) :=
      div_le_div_of_nonneg_right hc (by positivity)
    have h2 : 1 / (N * z.im) + PsiW (specOf A) z ^ 2 + (N : ℝ) ^ (-c₀ / 2) / (N * z.im) ≤
        6 * (1 / (N * z.im)) := by linarith
    have h3 : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hNp]; ring_nf
    have h0 : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hNp.le _
    calc (N : ℝ) ^ (ε / 2) * (1 / (N * z.im) + PsiW (specOf A) z ^ 2 +
          (N : ℝ) ^ (-c₀ / 2) / (N * z.im))
        ≤ (N : ℝ) ^ (ε / 2) * (6 * (1 / (N * z.im))) := mul_le_mul_of_nonneg_left h2 h0
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * (1 / (N * z.im))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 hv0) h0
      _ = (N : ℝ) ^ ε * (1 / (N * z.im)) := by rw [h3]; ring
  unfold ODomAt DomAt at hphi ⊢
  refine le_trans (measure_mono fun ω hω => ?_) hphi
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt hbound hω

/-- The strong form of Theorem 12.2 (ii) used in the proof of Theorem 12.4 (§12.4): the GOE averaged
error `Φ` is transferred with the extra error `Ψ² + N^{−c₀/2}(Nη)⁻¹`, for every `W` of the class. -/
theorem general_wig_avg_phi (τ c₀ : ℝ) (C : ℕ → ℝ) (ε D : ℝ) (hτ : 0 < τ) (hc₀ : 0 < c₀)
    (hε : 0 < ε) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (Φ : ℂ → ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ → WigClassEntries C N W → SpectralDomainW τ N S →
      StandingBoundW τ (specOf A) S →
      ((∀ i j, ∫ ω, W ω i j ^ 3 = 0) ∨ PsiSmallW c₀ (specOf A) S) →
      (∀ z ∈ S, 0 ≤ Φ z ∧ Φ z ≤ 1 / (N * z.im)) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S →
      AveragedPhiLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) S Φ →
      AveragedPhiLawWAt N ε D A W S
        (fun z => Φ z + PsiW (specOf A) z ^ 2 + (N : ℝ) ^ (-c₀ / 2) / (N * z.im)) :=
  avm_avg_phi τ c₀ C ε D hτ hc₀ hε

/-! ## Instances: `A = aEx N` (non-diagonal), Rademacher entries `wigRad N`, `τ = 1/2`

The hypotheses on the model are discharged at `(wigRad N, aEx N)`: `aEx N` is symmetric, not
diagonal and of norm at most `1/4 ≤ τ⁻¹`, the Rademacher entries lie in the class and satisfy (a),
the standing bound holds, and `S` contains `i`. The entrywise and averaged laws for the Gaussian
matrix are deformed local laws that cannot be discharged at a fixed `N`; they stay hypotheses, at
their natural scales: `Ψ` for the entrywise law, and `(Nη)⁻¹` for the averaged law, also in the form
with control `Φ = (Nη)⁻¹/2`. -/

section Instances

/-- `i ∈ 𝐃^W(1/2, N)` for `N ≥ 1`. -/
private lemma avm_I_mem_domW {N : ℕ} (hN : 1 ≤ N) : Complex.I ∈ domW (1 / 2) N := by
  refine ⟨by simp, by simp, ?_, by simp⟩
  simp only [Complex.I_im]
  exact Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 hN) (by norm_num)

/-- `0 ≤ (Nη)⁻¹/2 ≤ (Nη)⁻¹` for `η > 0`. -/
private lemma avm_phi_ex {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ 1 / (2 * (N * z.im)) ∧ 1 / (2 * (N * z.im)) ≤ 1 / (N * z.im) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) * z.im := mul_pos hNp hz
  refine ⟨by positivity, one_div_le_one_div_of_le hp (by linarith)⟩

/-- Theorem 12.2 (ii) along `N ≥ N₀` at `(wigRad N, aEx N)`, `τ = 1/2`, `S = 𝐃^W(1/2, N) ∋ i`,
`(ε, D) = (1/10, 1)`, case (a); conditional on the entrywise and averaged laws for the GOE. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N) →
    AveragedLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N) →
    Complex.I ∈ domW (1 / 2) N ∧
      AveragedLawWAt N (1 / 10) 1 (aEx N) (wigRad N) (domW (1 / 2) N) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    general_wig_avg (1 / 2) (1 / 12) (fun _ => 1) (1 / 10) 1 (by norm_num) (by norm_num)
      (by norm_num)
  exact ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 hg ha => ⟨avm_I_mem_domW hN1,
    h N hN (aEx N) (wigRad N) (domW (1 / 2) N) (wignerModel_rad hN1)
      (spectralDomainW_domW _ _) (standingBoundW_aEx hN1) (Or.inl (wigRad_third N)) hg ha⟩⟩

/-- The strong form along `N ≥ N₀` at `(wigRad N, aEx N)`, `τ = 1/2`, `S = 𝐃^W(1/2, N) ∋ i`,
`Φ = (Nη)⁻¹/2` (positive, below `(Nη)⁻¹`, at the averaged scale of the GOE), `(ε, D) = (1/10, 1)`,
case (a); conditional on the entrywise law and the averaged law with control `Φ` for the GOE. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N) →
    AveragedPhiLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (domW (1 / 2) N)
      (fun z => 1 / (2 * (N * z.im))) →
    Complex.I ∈ domW (1 / 2) N ∧ 0 < 1 / (2 * (N * Complex.I.im)) ∧
      AveragedPhiLawWAt N (1 / 10) 1 (aEx N) (wigRad N) (domW (1 / 2) N)
        (fun z => 1 / (2 * (N * z.im)) + PsiW (specOf (aEx N)) z ^ 2 +
          (N : ℝ) ^ (-(1 / 12 : ℝ) / 2) / (N * z.im)) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    general_wig_avg_phi (1 / 2) (1 / 12) (fun _ => 1) (1 / 10) 1 (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 hg ha => ⟨avm_I_mem_domW hN1, ?_, ?_⟩⟩
  · have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
    simp only [Complex.I_im, mul_one]
    positivity
  · exact h N hN (aEx N) (wigRad N) (domW (1 / 2) N)
      (fun z => 1 / (2 * (N * z.im))) (aEx_isHermitian N)
      ((norm_aEx_le hN1).trans (by norm_num)) (wignerEntries_wigRad hN1).toClass
      (spectralDomainW_domW _ _) (standingBoundW_aEx hN1) (Or.inl (wigRad_third N))
      (fun z hz => avm_phi_ex hN1 hz.1) hg ha

/-- `S_b = {z ∈ 𝐃^W(1/2, N) : Im z ≥ N^{−1/4}}`. -/
private def avmSb (N : ℕ) : Set ℂ := {z | z ∈ domW (1 / 2) N ∧ (N : ℝ) ^ (-1 / 4 : ℝ) ≤ z.im}

private lemma avmSb_spectral (N : ℕ) : SpectralDomainW (1 / 2) N (avmSb N) :=
  ⟨fun _ hz => hz.1, fun _ hz _ hw _ hle => ⟨hw, hz.2.trans hle⟩⟩

private lemma avmSb_I {N : ℕ} (hN : 1 ≤ N) : Complex.I ∈ avmSb N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨⟨by simp, by simp, ?_, by simp⟩, ?_⟩
  · simp only [Complex.I_im]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNr (by norm_num)
  · simp only [Complex.I_im]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNr (by norm_num)

/-- (b) of Theorem 12.2 on `S_b` with `c₀ = 1/100`: `Ψ ≤ N^{−3/8} + N^{−3/4} ≤ N^{−1/4−1/100}`. -/
private lemma avmSb_small {N : ℕ} (hN : 1024 ≤ N) :
    PsiSmallW (1 / 100) (specOf (aEx N)) (avmSb N) := by
  intro z hz
  have hN1 : 1 ≤ N := by omega
  have hNr : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hη : 0 < z.im := hz.1.1
  have hηl := hz.2
  have hm1 : (mW (specOf (aEx N)) z).im < 1 :=
    lt_of_le_of_lt (Complex.im_le_norm _) (norm_mW_lt_one hN1 _ hη)
  have hm0 : 0 < (mW (specOf (aEx N)) z).im := (mW_spec hN1 _ hη).1
  -- `1/(Nη) ≤ N^{−3/4}`
  have hq : 1 / (N * z.im) ≤ (N : ℝ) ^ (-3 / 4 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (N : ℝ) ^ (-3 / 4 : ℝ) * (N * (N : ℝ) ^ (-1 / 4 : ℝ)) = 1 := by
      rw [show (N : ℝ) * (N : ℝ) ^ (-1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) by
        rw [show (3 / 4 : ℝ) = 1 + (-1 / 4) by norm_num, Real.rpow_add hN0, Real.rpow_one],
        ← Real.rpow_add hN0]
      norm_num
    have h2 : (N : ℝ) ^ (-3 / 4 : ℝ) * (N * (N : ℝ) ^ (-1 / 4 : ℝ)) ≤
        (N : ℝ) ^ (-3 / 4 : ℝ) * (N * z.im) := by gcongr
    linarith
  have hs : Real.sqrt ((mW (specOf (aEx N)) z).im / (N * z.im)) ≤ (N : ℝ) ^ (-3 / 8 : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    calc (mW (specOf (aEx N)) z).im / (N * z.im) ≤ 1 / (N * z.im) := by
          gcongr
      _ ≤ (N : ℝ) ^ (-3 / 4 : ℝ) := hq
      _ = ((N : ℝ) ^ (-3 / 8 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have h34 : (N : ℝ) ^ (-3 / 4 : ℝ) ≤ (N : ℝ) ^ (-3 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (23 / 200 : ℝ) := by
    have h1 : (1024 : ℝ) ^ (23 / 200 : ℝ) ≤ (N : ℝ) ^ (23 / 200 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hNr (by norm_num)
    have h3 : (2 : ℝ) ≤ (1024 : ℝ) ^ (23 / 200 : ℝ) := by
      rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ (10 * (23 / 200) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hfin : 2 * (N : ℝ) ^ (-3 / 8 : ℝ) ≤ (N : ℝ) ^ (-1 / 4 - 1 / 100 : ℝ) := by
    have e1 : (N : ℝ) ^ (-1 / 4 - 1 / 100 : ℝ) =
        (N : ℝ) ^ (23 / 200 : ℝ) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    rw [e1]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  unfold PsiW
  linarith

/-- The strong form in case (b): `S_b = {z ∈ 𝐃^W(1/2, N) : Im z ≥ N^{−1/4}} ∋ i`, `c₀ = 1/100`,
`(wigRad N, aEx N)`, `Φ = (Nη)⁻¹/2`, `(ε, D) = (1/10, 1)`, with (b) discharged on `S_b`
for `N ≥ 2^{10}`; conditional on the entrywise law and the averaged law with control `Φ` for the
GOE. -/
example : ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1024 ≤ N →
    EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (avmSb N) →
    AveragedPhiLawWAt N ε₁ D₁ (diagonal (specOf (aEx N))) (goeW N) (avmSb N)
      (fun z => 1 / (2 * (N * z.im))) →
    Complex.I ∈ avmSb N ∧ PsiSmallW (1 / 100) (specOf (aEx N)) (avmSb N) ∧
      AveragedPhiLawWAt N (1 / 10) 1 (aEx N) (wigRad N) (avmSb N)
        (fun z => 1 / (2 * (N * z.im)) + PsiW (specOf (aEx N)) z ^ 2 +
          (N : ℝ) ^ (-(1 / 100 : ℝ) / 2) / (N * z.im)) := by
  obtain ⟨ε₁, D₁, hε₁, N₀, h⟩ :=
    general_wig_avg_phi (1 / 2) (1 / 100) (fun _ => 1) (1 / 10) 1 (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨ε₁, D₁, hε₁, N₀, fun N hN hN1 hg ha =>
    ⟨avmSb_I (by omega), avmSb_small hN1, ?_⟩⟩
  have hN1' : 1 ≤ N := by omega
  exact h N hN (aEx N) (wigRad N) (avmSb N)
    (fun z => 1 / (2 * (N * z.im))) (aEx_isHermitian N)
    ((norm_aEx_le hN1').trans (by norm_num)) (wignerEntries_wigRad hN1').toClass
    (avmSb_spectral N) (fun z hz => standingBoundW_aEx hN1' z hz.1) (Or.inr (avmSb_small hN1))
    (fun z hz => avm_phi_ex hN1' hz.1.1) hg ha

end Instances

#print axioms general_wig_avg
#print axioms general_wig_avg_phi

end Anisotropic

