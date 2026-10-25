import Anisotropic.EdgeUniv.SmCount
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.DominationUnion
import Anisotropic.Framework.Model
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.EdgeLocal
import Anisotropic.Wigner.EdgeSqrt
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The edge regime for `W + A` and for the GOE plus `D` -/

/-- The real orthogonal matrix of eigenvectors of a symmetric `A`, with `U Uᵀ = 1`, `Uᵀ U = 1`
and `A = U diag(λ) Uᵀ`. -/
private lemma aux_eig_decomp {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
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

/-- `N⁻¹ tr (W + A − z)⁻¹ = N⁻¹ ∑_k (λ_k − z)⁻¹` for the symmetric `W + A` and `Im z > 0`. -/
private lemma aux_mNW_sum {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    mNW A Wm z = (N : ℂ)⁻¹ * ∑ k, ((specOf (Wm + A) k : ℂ) - z)⁻¹ := by
  obtain ⟨U, hUU, hUU', hAU⟩ := aux_eig_decomp hH
  set l := hH.eigenvalues with hl
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hP : cplx U * (cplx U)ᵀ = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hP' : (cplx U)ᵀ * cplx U = 1 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hM : cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (l k : ℂ) - z) * (cplx U)ᵀ := by
    have h1 : cplx (Wm + A) = cplx U * diagonal (fun k => (l k : ℂ)) * (cplx U)ᵀ := by
      rw [hAU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (l k : ℂ) - z) =
        diagonal (fun k => (l k : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  have hinv : (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hM]
    calc cplx U * diagonal (fun k => (l k : ℂ) - z) * (cplx U)ᵀ *
          (cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ)
        = cplx U * diagonal (fun k => (l k : ℂ) - z) * ((cplx U)ᵀ * cplx U) *
          diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hP', Matrix.mul_one, Matrix.mul_assoc (cplx U), Matrix.diagonal_mul_diagonal]
          have : (fun k => ((l k : ℂ) - z) * ((l k : ℂ) - z)⁻¹) = fun _ => 1 := by
            funext k
            exact mul_inv_cancel₀ (hne k)
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hP]
  unfold mNW GW
  rw [hinv, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.trace_diagonal,
    specOf_eq hH]

/-- `Im N⁻¹ tr G^W(z) = N⁻¹ ∑_k η / ((λ_k - E)² + η²)`, `λ_k` the eigenvalues of `W + A`. -/
theorem im_mNW_eq {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    (mNW A Wm z).im =
      (N : ℝ)⁻¹ * ∑ k, z.im / ((specOf (Wm + A) k - z.re) ^ 2 + z.im ^ 2) := by
  rw [aux_mNW_sum (hW.add hA) hz]
  have hc : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `N η Im N⁻¹ tr G^W(E + iη) = ∑_k η² / ((λ_k - E)² + η²)`. -/
private lemma aux_N_im_mNW {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) (E : ℝ) {η : ℝ} (hη : 0 < η) :
    N * η * (mNW A Wm (E + η * Complex.I)).im =
      ∑ k, η ^ 2 / ((specOf (Wm + A) k - E) ^ 2 + η ^ 2) := by
  have hz : 0 < (E + η * Complex.I : ℂ).im := by simpa using hη
  rw [im_mNW_eq hA hW hz]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp

/-- The local count: `#{k : |λ_k - E| ≤ r} ≤ 2 N r Im N⁻¹ tr G^W(E + i r)`. -/
theorem card_eig_near_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) (E : ℝ) {r : ℝ} (hr : 0 < r) :
    (((Finset.univ.filter fun k => |specOf (Wm + A) k - E| ≤ r).card : ℕ) : ℝ) ≤
      2 * N * r * (mNW A Wm (E + r * Complex.I)).im := by
  have h := aux_N_im_mNW hA hW E hr
  rw [show 2 * (N : ℝ) * r * (mNW A Wm (E + r * Complex.I)).im =
    2 * (N * r * (mNW A Wm (E + r * Complex.I)).im) by ring, h, Finset.mul_sum,
    Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hd : 0 < (specOf (Wm + A) k - E) ^ 2 + r ^ 2 := by positivity
  split_ifs with hk
  · have hsq : (specOf (Wm + A) k - E) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hk 2
    rw [Nat.cast_one, mul_div_assoc', le_div_iff₀ hd]
    linarith
  · rw [Nat.cast_zero]
    positivity

/-- The two-point lower count: for `κ ≥ 2`,
`N η (Im m_N(E + iη) - (2/κ) Im m_N(E + iκη)) ≤ #{k : |λ_k - E| < √(κ² - 2) η}`. -/
theorem card_eig_near_ge {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) (E : ℝ) {η κ : ℝ} (hη : 0 < η) (hκ : 2 ≤ κ) :
    N * η * ((mNW A Wm (E + η * Complex.I)).im -
        2 / κ * (mNW A Wm (E + κ * η * Complex.I)).im) ≤
      (((Finset.univ.filter fun k =>
        |specOf (Wm + A) k - E| < Real.sqrt (κ ^ 2 - 2) * η).card : ℕ) : ℝ) := by
  have hκ0 : 0 < κ := by linarith
  have hκη : 0 < κ * η := mul_pos hκ0 hη
  have h1 := aux_N_im_mNW hA hW E hη
  have h2 := aux_N_im_mNW hA hW E hκη
  have hpt : ((E : ℂ) + ((κ * η : ℝ) : ℂ) * Complex.I) = E + κ * η * Complex.I := by push_cast; ring
  rw [hpt] at h2
  have hsplit : N * η * ((mNW A Wm (E + η * Complex.I)).im -
        2 / κ * (mNW A Wm (E + κ * η * Complex.I)).im) =
      N * η * (mNW A Wm (E + η * Complex.I)).im -
        2 / κ ^ 2 * (N * (κ * η) * (mNW A Wm (E + κ * η * Complex.I)).im) := by
    field_simp
  rw [hsplit, h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  set u := specOf (Wm + A) k - E
  have hd1 : 0 < u ^ 2 + η ^ 2 := by positivity
  have hd2 : 0 < u ^ 2 + (κ * η) ^ 2 := by positivity
  have hfirst : η ^ 2 / (u ^ 2 + η ^ 2) ≤ 1 := by
    rw [div_le_one hd1]; nlinarith [sq_nonneg u]
  have hsecond : 0 ≤ 2 / κ ^ 2 * ((κ * η) ^ 2 / (u ^ 2 + (κ * η) ^ 2)) := by positivity
  split_ifs with hk
  · rw [Nat.cast_one]
    linarith
  · rw [Nat.cast_zero]
    push Not at hk
    have hs : 0 ≤ κ ^ 2 - 2 := by nlinarith
    have hsq : (κ ^ 2 - 2) * η ^ 2 ≤ u ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hk 2
      rwa [mul_pow, Real.sq_sqrt hs, sq_abs] at this
    have hκ2 : 2 / κ ^ 2 * ((κ * η) ^ 2 / (u ^ 2 + (κ * η) ^ 2)) =
        2 * η ^ 2 / (u ^ 2 + (κ * η) ^ 2) := by
      field_simp
    rw [hκ2, sub_nonpos, div_le_div_iff₀ hd1 hd2]
    nlinarith [sq_nonneg η]

/-- `t^{3/2} = t √t` for `t ≥ 0`. -/
private lemma aux_rpow_three_halves {t : ℝ} (ht : 0 ≤ t) : t ^ (3 / 2 : ℝ) = t * √t := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ht (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The arithmetic of the two-point lower count at `E = L₊ - s/2`, `η₁ = s/(2κ)`,
`s = (q u²)²`, `N q³ = 1`, `κ = 16 K²`: from `Im m^W(E + iη₁) ≥ K⁻¹ √(s/2 + η₁)`,
`Im m^W(E + iκη₁) ≤ K √(s/2 + κη₁)` and the two averaged errors `u² B/(N η)`, the left side of
the two-point count is at least `u⁶/(4κK) - 2Bu² ≥ l`. -/
private lemma aux_clause3_arith {N q u K B X Y mx my : ℝ} {l : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hu : 1 ≤ u) (hK1 : 1 ≤ K) (hB : 0 ≤ B) (hNq : N * q ^ 3 = 1)
    (hbig : 4 * (16 * K ^ 2) * K * (2 * B + l) ≤ u ^ 4)
    (hX : mx - u ^ 2 * B / (N * ((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2)))) ≤ X)
    (hY : Y ≤ my + u ^ 2 * B /
      (N * ((16 * K ^ 2) * ((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2))))))
    (hmx : K⁻¹ * √((q * u ^ 2) ^ 2 / 2 + (q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2))) ≤ mx)
    (hmy : my ≤ K * √((q * u ^ 2) ^ 2 / 2 +
      (16 * K ^ 2) * ((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2))))) :
    (l : ℝ) ≤ N * ((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2))) *
      (X - 2 / (16 * K ^ 2) * Y) := by
  have hK : 0 < K := by linarith
  set κ := 16 * K ^ 2 with hκ
  set w := q * u ^ 2 with hw
  have hκ0 : 0 < κ := by positivity
  have hw0 : 0 < w := by positivity
  set η := w ^ 2 / (2 * κ) with hη
  have hη0 : 0 < η := by positivity
  have hNη : 0 < N * η := mul_pos hN hη0
  have hκη : κ * η = w ^ 2 / 2 := by rw [hη]; field_simp
  -- the deterministic bounds
  have hmx' : 5 / 8 * w / K ≤ mx := by
    refine le_trans ?_ hmx
    have h1 : 5 / 8 * w ≤ √(w ^ 2 / 2 + η) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith [hη0]
    calc 5 / 8 * w / K = K⁻¹ * (5 / 8 * w) := by ring
      _ ≤ K⁻¹ * √(w ^ 2 / 2 + η) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hmy' : my ≤ K * w := by
    refine hmy.trans (le_of_eq ?_)
    rw [hκη, show w ^ 2 / 2 + w ^ 2 / 2 = w ^ 2 by ring, Real.sqrt_sq hw0.le]
  -- the errors
  have he1 : N * η * (u ^ 2 * B / (N * η)) = u ^ 2 * B := by field_simp
  have he2 : N * η * (2 / κ * (u ^ 2 * B / (N * (κ * η)))) = 2 / κ ^ 2 * (u ^ 2 * B) := by
    field_simp
  have hNw : N * η * w = u ^ 6 / (2 * κ) := by
    rw [hη, hw]
    have : N * ((q * u ^ 2) ^ 2 / (2 * κ)) * (q * u ^ 2) = (N * q ^ 3) * u ^ 6 / (2 * κ) := by
      ring
    rw [this, hNq, one_mul]
  have hX' : N * η * (5 / 8 * w / K) - u ^ 2 * B ≤ N * η * X := by
    have := mul_le_mul_of_nonneg_left (hmx'.trans (by linarith [hX] : mx ≤ X +
      u ^ 2 * B / (N * η))) hNη.le
    rw [mul_add, he1] at this
    linarith
  have hY' : N * η * (2 / κ * Y) ≤ N * η * (2 / κ * (K * w)) + 2 / κ ^ 2 * (u ^ 2 * B) := by
    have h2 : 2 / κ * Y ≤ 2 / κ * (K * w) + 2 / κ * (u ^ 2 * B / (N * (κ * η))) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hY.trans (by linarith [hmy'])) (by positivity)
    have := mul_le_mul_of_nonneg_left h2 hNη.le
    rw [mul_add, he2] at this
    exact this
  have hmain : N * η * (5 / 8 * w / K) - N * η * (2 / κ * (K * w)) = u ^ 6 / (4 * κ * K) := by
    have e1 : N * η * (5 / 8 * w / K) = 5 / 8 / K * (N * η * w) := by ring
    have e2 : N * η * (2 / κ * (K * w)) = 2 * K / κ * (N * η * w) := by ring
    rw [e1, e2, hNw, hκ]
    field_simp
    ring
  have hκ2 : 2 / κ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 16 ≤ κ := by rw [hκ]; nlinarith [hK]
    nlinarith
  have herr : 2 / κ ^ 2 * (u ^ 2 * B) ≤ u ^ 2 * B :=
    mul_le_of_le_one_left (by positivity) hκ2
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu
  have hfin : (l : ℝ) + 2 * (u ^ 2 * B) ≤ u ^ 6 / (4 * κ * K) := by
    rw [le_div_iff₀ (by positivity)]
    have h6 : u ^ 6 = u ^ 4 * u ^ 2 := by ring
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have h1 : 4 * κ * K * (2 * B + l) * u ^ 2 ≤ u ^ 4 * u ^ 2 :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    have h2 : (l : ℝ) ≤ l * u ^ 2 := le_mul_of_one_le_right hl hu2
    have h3 : 0 ≤ 4 * κ * K := by positivity
    have h4 : 4 * κ * K * l ≤ 4 * κ * K * (l * u ^ 2) := mul_le_mul_of_nonneg_left h2 h3
    rw [h6]
    nlinarith
  rw [mul_sub]
  linarith

/-- The arithmetic of the upper count at the grid point `E = L₊ - n t₀/2`, `r = (n+2) t₀/2`,
`t₀ = (q u)²`, `N q³ = 1`: from `Im m^W(E + ir) ≤ K √((n+1) t₀)` and the averaged error
`u² B/(N r)`, `2 N r Im m_N(E + ir) ≤ u⁴ + 6 K N t^{3/2}` whenever `n t₀ ≤ t`. -/
private lemma aux_clause4_arith {N q u K B Y my t : ℝ} {n : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hu : 1 ≤ u) (hK : 0 < K) (hNq : N * q ^ 3 = 1)
    (hsmall : 2 * K * u ^ 3 + 2 * B * u ^ 2 ≤ u ^ 4)
    (ht : n * (q * u) ^ 2 ≤ t)
    (hY : Y ≤ my + u ^ 2 * B / (N * ((n + 2) * (q * u) ^ 2 / 2)))
    (hmy : my ≤ K * √((n + 1) * (q * u) ^ 2)) :
    2 * N * ((n + 2) * (q * u) ^ 2 / 2) * Y ≤ u ^ 4 + 6 * K * N * t ^ (3 / 2 : ℝ) := by
  set v := q * u with hv
  have hv0 : 0 < v := by positivity
  set r := (n + 2) * v ^ 2 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hNr : 0 < 2 * N * r := by positivity
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have h1 : 2 * N * r * Y ≤ 2 * N * r * (K * √((n + 1) * v ^ 2)) + 2 * (u ^ 2 * B) := by
    have := mul_le_mul_of_nonneg_left (hY.trans (by linarith [hmy] :
      my + u ^ 2 * B / (N * r) ≤ K * √((n + 1) * v ^ 2) + u ^ 2 * B / (N * r))) hNr.le
    rw [mul_add] at this
    have e : 2 * N * r * (u ^ 2 * B / (N * r)) = 2 * (u ^ 2 * B) := by field_simp
    rw [e] at this
    exact this
  have hK3 : 0 ≤ K * u ^ 3 := by positivity
  have hrhs : 0 ≤ 6 * K * N * t ^ (3 / 2 : ℝ) := by
    have := Real.rpow_nonneg ht0 (3 / 2 : ℝ)
    positivity
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hs : √((((0 : ℕ) : ℝ) + 1) * v ^ 2) = v := by
      rw [Nat.cast_zero, zero_add, one_mul, Real.sqrt_sq hv0.le]
    rw [hs] at h1
    have e : 2 * N * r * (K * v) = 2 * K * u ^ 3 := by
      rw [hr, hv]
      have : 2 * N * ((((0 : ℕ) : ℝ) + 2) * (q * u) ^ 2 / 2) * (K * (q * u)) =
          2 * K * (N * q ^ 3) * u ^ 3 := by push_cast; ring
      rw [this, hNq, mul_one]
    rw [e] at h1
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have h2r : 2 * r ≤ 3 * t := by
      rw [hr]; nlinarith [sq_nonneg v]
    have hsq : √((n + 1) * v ^ 2) ≤ 2 * √t := by
      have : (n + 1) * v ^ 2 ≤ 4 * t := by nlinarith [sq_nonneg v]
      calc √((n + 1) * v ^ 2) ≤ √(4 * t) := Real.sqrt_le_sqrt this
        _ = 2 * √t := by
          rw [Real.sqrt_mul' _ ht0, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hst : 0 ≤ √t := Real.sqrt_nonneg t
    have h3 : 2 * N * r * (K * √((n + 1) * v ^ 2)) ≤ 6 * K * N * (t * √t) := by
      have hA : 2 * N * r * (K * √((n + 1) * v ^ 2)) = N * K * (2 * r) * √((n + 1) * v ^ 2) := by
        ring
      rw [hA]
      have hNK : 0 ≤ N * K := by positivity
      calc N * K * (2 * r) * √((n + 1) * v ^ 2) ≤ N * K * (3 * t) * (2 * √t) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h2r hNK) hsq (Real.sqrt_nonneg _)
            positivity
        _ = 6 * K * N * (t * √t) := by ring
    rw [aux_rpow_three_halves ht0]
    nlinarith

/-- A point `E + ir` with `|E - L₊| ≤ c ≤ 1`, `|E - L₊| ≤ K r` and `N^{-2/3} ≤ r ≤ 1` lies in
the edge cone, when `|L₊| ≤ τ⁻¹ - 1` and `τ ≤ 1/4`. -/
private lemma aux_mem_cone {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) {N : ℕ} (hN : 1 ≤ N)
    {a : Fin N → ℝ} (hL : |LpW a| ≤ τ⁻¹ - 1) {c K E r : ℝ} (hc1 : c ≤ 1)
    (hEc : |E - LpW a| ≤ c) (hEK : |E - LpW a| ≤ K * r) (hr : (N : ℝ) ^ (-2 / 3 : ℝ) ≤ r)
    (hr1 : r ≤ 1) : ((E : ℂ) + r * Complex.I) ∈ edgeConeW τ N a c K := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr0 : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hr
  have hτinv : 4 ≤ τ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτ]
    linarith
  have hre : ((E : ℂ) + r * Complex.I).re = E := by simp
  have him : ((E : ℂ) + r * Complex.I).im = r := by simp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [hre, him]
  · exact hr0
  · have : |E| ≤ |E - LpW a| + |LpW a| := by
      have := abs_add_le (E - LpW a) (LpW a)
      rwa [sub_add_cancel] at this
    linarith
  · refine le_trans ?_ hr
    exact Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
  · linarith
  · exact hr
  · exact hEc
  · exact hEK

/-- Every eigenvalue is at most `λ₁`. -/
private lemma aux_spec_le_sortedEig {N : ℕ} (hN : 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (k : Fin N) : specOf H k ≤ sortedEig H 1 := by
  rw [sortedEig_ge_iff hH le_rfl hN]
  unfold eigCount
  exact Finset.card_pos.2 ⟨k, by simp⟩

/-- No eigenvalue `≥ X` when all eigenvalues are `< X`. -/
private lemma aux_eigCount_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {X : ℝ}
    (h : ∀ k, specOf H k < X) : eigCount H X = 0 := by
  unfold eigCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _
  exact not_le.2 (h k)

/-- The deterministic part of the edge regime: with `t₀ = (q u)²`, `s = (q u²)² = N^{-2/3+δ}`,
`κ = 16 K²`, if every eigenvalue of `Wm + A` is `≤ L + t₀`, `m` satisfies the square-root bounds
`K^{∓1} √(L - E + η)` within `c₁` of `L` below `L`, and `Im N⁻¹ tr G^W` is within `u² B/(N η)`
of `Im m` at the two points `L - s/2 + iη₁`, `L - s/2 + iκη₁` (`η₁ = s/(2κ)`) and at the grid
points `L - n t₀/2 + i(n+2) t₀/2`, `n t₀ ≤ c₁/8`, then `Wm + A` is in the edge regime at `L`. -/
private lemma aux_regime_det {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) (hN1 : 1 ≤ N) {mf : ℂ → ℂ} {L q u K c₁ B δ : ℝ} {l : ℕ}
    (hq0 : 0 < q) (hu1 : 1 ≤ u) (hNq : (N : ℝ) * q ^ 3 = 1) (hu4 : (N : ℝ) ^ δ = u ^ 4)
    (hspow : (N : ℝ) ^ (-2 / 3 + δ) = (q * u ^ 2) ^ 2) (hK1 : 1 ≤ K) (hB0 : 0 ≤ B)
    (hbig : 4 * (16 * K ^ 2) * K * (2 * B + l) ≤ u ^ 4)
    (hsmall : 2 * K * u ^ 3 + 2 * B * u ^ 2 ≤ u ^ 4)
    (hss : (q * u ^ 2) ^ 2 ≤ c₁ / 8) (ht₀s : (q * u) ^ 2 < (q * u ^ 2) ^ 2)
    (hsq : ∀ z : ℂ, 0 < z.im → |z.re - L| + z.im ≤ c₁ → z.re ≤ L →
      K⁻¹ * √(L - z.re + z.im) ≤ (mf z).im ∧ (mf z).im ≤ K * √(L - z.re + z.im))
    (hlam : ∀ k, specOf (Wm + A) k ≤ L + (q * u) ^ 2)
    (hlaw1 : |(mNW A Wm (((L - (q * u ^ 2) ^ 2 / 2 : ℝ) : ℂ) +
        (((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2)) : ℝ) : ℂ) * Complex.I)).im -
      (mf (((L - (q * u ^ 2) ^ 2 / 2 : ℝ) : ℂ) +
        (((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2)) : ℝ) : ℂ) * Complex.I)).im| ≤
      u ^ 2 * B / (N * ((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2)))))
    (hlaw2 : |(mNW A Wm (((L - (q * u ^ 2) ^ 2 / 2 : ℝ) : ℂ) + ((16 * K ^ 2 : ℝ) : ℂ) *
        (((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2)) : ℝ) : ℂ) * Complex.I)).im -
      (mf (((L - (q * u ^ 2) ^ 2 / 2 : ℝ) : ℂ) + ((16 * K ^ 2 : ℝ) : ℂ) *
        (((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2)) : ℝ) : ℂ) * Complex.I)).im| ≤
      u ^ 2 * B / (N * ((16 * K ^ 2) * ((q * u ^ 2) ^ 2 / (2 * (16 * K ^ 2))))))
    (hlawg : ∀ n : ℕ, (n : ℝ) * (q * u) ^ 2 ≤ c₁ / 8 →
      |(mNW A Wm (((L - n * (q * u) ^ 2 / 2 : ℝ) : ℂ) +
        (((n + 2) * (q * u) ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).im -
      (mf (((L - n * (q * u) ^ 2 / 2 : ℝ) : ℂ) +
        (((n + 2) * (q * u) ^ 2 / 2 : ℝ) : ℂ) * Complex.I)).im| ≤
      u ^ 2 * B / (N * ((n + 2) * (q * u) ^ 2 / 2))) :
    EdgeRegime N L 0 l δ (c₁ / 8) (6 * K) (Wm + A) := by
  have hNr0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hK0 : 0 < K := by linarith
  set κ := 16 * K ^ 2 with hκ
  have hκ16 : 16 ≤ κ := by nlinarith
  set s := (q * u ^ 2) ^ 2 with hs
  set t₀ := (q * u) ^ 2 with ht₀
  have hs0 : 0 < s := by positivity
  have ht₀0 : 0 < t₀ := by positivity
  have hc₁0 : 0 < c₁ := by linarith
  set η₁ := s / (2 * κ) with hη₁
  have hη₁0 : 0 < η₁ := by positivity
  set E₃ := L - s / 2 with hE₃
  have hκη₁ : κ * η₁ = s / 2 := by rw [hη₁]; field_simp
  have hE₃L : |E₃ - L| = s / 2 := by
    rw [hE₃, show L - s / 2 - L = -(s / 2) by ring, abs_neg, abs_of_pos (by positivity)]
  have hη₁s : η₁ ≤ s / 2 := by
    rw [← hκη₁]
    exact le_mul_of_one_le_left hη₁0.le (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine aux_eigCount_zero fun k => ?_
    rw [hspow]
    linarith [hlam k]
  · refine aux_eigCount_zero fun k => ?_
    linarith [hlam k]
  · rw [hspow, zero_add]
    have hcount := card_eig_near_ge hA hW E₃ hη₁0 (by linarith : (2 : ℝ) ≤ κ)
    have hsub : ((Finset.univ.filter fun k =>
        |specOf (Wm + A) k - E₃| < Real.sqrt (κ ^ 2 - 2) * η₁).card : ℕ) ≤
        eigCount (Wm + A) (L - s) := by
      unfold eigCount
      refine Finset.card_le_card fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      have hsk : Real.sqrt (κ ^ 2 - 2) ≤ κ := by
        calc Real.sqrt (κ ^ 2 - 2) ≤ Real.sqrt (κ ^ 2) := Real.sqrt_le_sqrt (by linarith)
          _ = κ := Real.sqrt_sq (by linarith)
      have : Real.sqrt (κ ^ 2 - 2) * η₁ ≤ κ * η₁ := mul_le_mul_of_nonneg_right hsk hη₁0.le
      have := (abs_lt.1 (lt_of_lt_of_le hk (this.trans hκη₁.le))).1
      linarith
    have hpt2 : ((E₃ : ℂ) + κ * η₁ * Complex.I) =
        ((E₃ : ℂ) + ((κ : ℝ) : ℂ) * ((η₁ : ℝ) : ℂ) * Complex.I) := rfl
    have h1im : ((E₃ : ℂ) + η₁ * Complex.I).im = η₁ := by simp
    have h1re : ((E₃ : ℂ) + η₁ * Complex.I).re = E₃ := by simp
    have h2im : ((E₃ : ℂ) + κ * η₁ * Complex.I).im = κ * η₁ := by simp
    have h2re : ((E₃ : ℂ) + κ * η₁ * Complex.I).re = E₃ := by simp
    have hsq1 := (hsq ((E₃ : ℂ) + η₁ * Complex.I) (by rw [h1im]; exact hη₁0)
      (by rw [h1re, h1im, hE₃L]; linarith) (by rw [h1re]; linarith)).1
    have hsq2 := (hsq ((E₃ : ℂ) + κ * η₁ * Complex.I) (by rw [h2im]; positivity)
      (by rw [h2re, h2im, hE₃L, hκη₁]; linarith) (by rw [h2re]; linarith)).2
    rw [h1re, h1im] at hsq1
    rw [h2re, h2im] at hsq2
    have hLE : L - E₃ = s / 2 := by rw [hE₃]; ring
    rw [hLE] at hsq1 hsq2
    have harith := aux_clause3_arith (l := l) hNr0 hq0 hu1 hK1 hB0 hNq hbig
      (X := (mNW A Wm ((E₃ : ℂ) + η₁ * Complex.I)).im)
      (Y := (mNW A Wm ((E₃ : ℂ) + κ * η₁ * Complex.I)).im)
      (mx := (mf ((E₃ : ℂ) + η₁ * Complex.I)).im)
      (my := (mf ((E₃ : ℂ) + κ * η₁ * Complex.I)).im)
      (by linarith [(abs_le.1 hlaw1).1])
      (by linarith [(abs_le.1 hlaw2).2])
      hsq1 hsq2
    have : (l : ℝ) ≤ eigCount (Wm + A) (L - s) :=
      le_trans (le_trans harith hcount) (by exact_mod_cast hsub)
    exact_mod_cast this
  · intro t ht
    rw [Nat.cast_zero, sub_zero, hu4]
    obtain ⟨ht0, htr⟩ := ht
    set n := ⌊t / t₀⌋₊ with hn
    have hnt : (n : ℝ) * t₀ ≤ t := by
      have := Nat.floor_le (div_nonneg ht0 ht₀0.le)
      rw [← hn, le_div_iff₀ ht₀0] at this
      exact this
    have htn : t ≤ (n + 1) * t₀ := by
      have := Nat.lt_floor_add_one (t / t₀)
      rw [← hn, div_lt_iff₀ ht₀0] at this
      linarith
    have h1 : (n : ℝ) * t₀ ≤ c₁ / 8 := hnt.trans htr
    set E := L - n * t₀ / 2 with hE
    set r := (n + 2) * t₀ / 2 with hr
    have hr0 : 0 < r := by positivity
    have hnt0 : (0 : ℝ) ≤ n * t₀ := by positivity
    have hsub : eigCount (Wm + A) (L - t) ≤
        (Finset.univ.filter fun k => |specOf (Wm + A) k - E| ≤ r).card := by
      unfold eigCount
      refine Finset.card_le_card fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rw [abs_le]
      have := hlam k
      constructor <;> linarith
    have hcount := card_eig_near_le hA hW E hr0
    have hgim : ((E : ℂ) + r * Complex.I).im = r := by simp
    have hgre : ((E : ℂ) + r * Complex.I).re = E := by simp
    have hgE : |E - L| = n * t₀ / 2 := by
      rw [hE, show L - n * t₀ / 2 - L = -(n * t₀ / 2) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have hsq3 := (hsq ((E : ℂ) + r * Complex.I) (by rw [hgim]; exact hr0)
      (by rw [hgre, hgim, hgE]; linarith) (by rw [hgre]; linarith)).2
    rw [hgre, hgim, show L - E + r = (n + 1) * t₀ by rw [hE, hr]; ring] at hsq3
    have harith := aux_clause4_arith (n := n) hNr0 hq0 hu1 hK0 hNq hsmall hnt
      (Y := (mNW A Wm ((E : ℂ) + r * Complex.I)).im) (my := (mf ((E : ℂ) + r * Complex.I)).im)
      (by linarith [(abs_le.1 (hlawg n h1)).2]) hsq3
    have := le_trans (Nat.cast_le.2 hsub) (le_trans hcount harith)
    simpa [mul_assoc] using this

/-- The edge regime at `L₊` with probability `≥ 1 - N^{-1}`, at every exponent `δ ∈ (0, 1/3]`,
for `W + A` with any random symmetric `W`: from the averaged law with control `C_Φ (Nη)⁻¹` on
the edge cone and the rigid extremes, both at `(δ/2, 3)` (no eigenvalue beyond
`L₊ + N^{-2/3+δ}`; at least `l` eigenvalues above `L₊ - N^{-2/3+δ}` by a two-point count; at
most `N^δ + C₀ N t^{3/2}` above `L₊ - t`, by a uniform grid and `Im m^W ≍ √(κ + η)`). -/
theorem edgeRegime_wig {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) :
    ∃ c K r₀ C₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < r₀ ∧ 1 ≤ C₀ ∧
      ∀ (δ CΦ : ℝ) (l : ℕ), 0 < δ → δ ≤ 1 / 3 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
        A.IsHermitian → (∀ ω, (W ω).IsHermitian) → (∀ i, |specOf A i| ≤ τ⁻¹ - 3) →
        StandingBoundW τ (specOf A) (domW τ N) →
        AveragedPhiLawWAt N (δ / 2) 3 A W (edgeConeW τ N (specOf A) c K)
          (fun z => CΦ / (N * z.im)) →
        RigidExtremesWAt N (δ / 2) 3 (specOf A) (fun ω => W ω + A) →
        HighProbAt N 1 {ω | EdgeRegime N (LpW (specOf A)) 0 l δ r₀ C₀ (W ω + A)} := by
  obtain ⟨cs, Ks, hcs, hKs, Ns, hsq⟩ := im_mW_sqrt_edge hτ
  set K₁ := max Ks 1 with hK₁
  have hK₁1 : 1 ≤ K₁ := le_max_right _ _
  have hK₁0 : 0 < K₁ := by linarith
  have hKinv : K₁⁻¹ ≤ Ks⁻¹ := inv_anti₀ hKs (le_max_left _ _)
  set c₁ := min cs 1 with hc₁
  have hc₁0 : 0 < c₁ := lt_min hcs one_pos
  have hc₁cs : c₁ ≤ cs := min_le_left _ _
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  set κ := 16 * K₁ ^ 2 with hκ
  have hκ16 : 16 ≤ κ := by nlinarith
  refine ⟨c₁, κ, c₁ / 8, 6 * K₁, hc₁0, by linarith, by positivity, by linarith, ?_⟩
  intro δ CΦ l hδ hδ3
  set B := |CΦ| with hB
  have hB0 : 0 ≤ B := abs_nonneg _
  set Mu := max (max (2 * K₁ + 2 * B + 1) (4 * κ * K₁ * (2 * B + l) + 1)) (2 * κ + 1) with hMu
  have ev1 : ∀ᶠ N : ℕ in atTop, Mu ≤ (N : ℝ) ^ (δ / 4) :=
    ((tendsto_rpow_atTop (by linarith : 0 < δ / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop Mu
  have ev2 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-2 / 3 + δ) ≤ c₁ / 8 := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 / 3 - δ)).comp
      tendsto_natCast_atTop_atTop
    refine (h.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < c₁ / 8))).mono fun N hN => ?_
    simp only [Function.comp] at hN
    rwa [show -(2 / 3 - δ) = -2 / 3 + δ by ring] at hN
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (ev1.and (ev2.and (eventually_ge_atTop (max Ns 3))))
  refine ⟨N₀, fun N hN Ω _ _ A W hA hW ha hSB hav hrig => ?_⟩
  obtain ⟨hMuN, hsN, hNbig⟩ := hN₀ N hN
  have hNs : Ns ≤ N := le_of_max_le_left hNbig
  have hN3 : 3 ≤ N := le_of_max_le_right hNbig
  have hN1 : 1 ≤ N := by omega
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNr0 : (0 : ℝ) < N := by linarith
  -- the powers `q = N^{-1/3}` and `u = N^{δ/4}`
  set q := (N : ℝ) ^ (-1 / 3 : ℝ) with hq
  set u := (N : ℝ) ^ (δ / 4) with hu
  have hq0 : 0 < q := Real.rpow_pos_of_pos hNr0 _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr1 (by norm_num)
  have hMu1 : 1 ≤ Mu := le_trans (by linarith) (le_max_right _ _)
  have hu1 : 1 ≤ u := le_trans hMu1 hMuN
  have hNq : (N : ℝ) * q ^ 3 = 1 := by
    rw [hq, ← Real.rpow_mul_natCast hNr0.le,
      show (-1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one,
      mul_inv_cancel₀ hNr0.ne']
  have hp : (N : ℝ) ^ (-2 / 3 : ℝ) = q ^ 2 := by
    rw [hq, ← Real.rpow_mul_natCast hNr0.le]
    congr 1
    push_cast
    ring
  have hu4 : (N : ℝ) ^ δ = u ^ 4 := by
    rw [hu, ← Real.rpow_mul_natCast hNr0.le]
    congr 1
    push_cast
    ring
  have hu2 : (N : ℝ) ^ (δ / 2) = u ^ 2 := by
    rw [hu, ← Real.rpow_mul_natCast hNr0.le]
    congr 1
    push_cast
    ring
  have hspow : (N : ℝ) ^ (-2 / 3 + δ) = (q * u ^ 2) ^ 2 := by
    rw [Real.rpow_add hNr0, hp, hu4]
    ring
  set s := (q * u ^ 2) ^ 2 with hs
  set t₀ := (q * u) ^ 2 with ht₀
  have hs0 : 0 < s := by positivity
  have ht₀0 : 0 < t₀ := by positivity
  have hss : s ≤ c₁ / 8 := hspow ▸ hsN
  have huu : u ≤ u ^ 4 := le_self_pow₀ hu1 (by norm_num)
  have hMu_a : 2 * K₁ + 2 * B + 1 ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMuN
  have hMu_b : 4 * κ * K₁ * (2 * B + l) ≤ u ^ 4 := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMuN
    linarith
  have hMu_c : 2 * κ ≤ u ^ 4 := by
    have := le_trans (le_max_right _ _) hMuN
    linarith
  have hu23 : u ^ 2 ≤ u ^ 3 := pow_le_pow_right₀ hu1 (by norm_num)
  have h7 : 2 * K₁ * u ^ 3 + 2 * B * u ^ 2 ≤ u ^ 4 := by
    have hu3 : 0 ≤ u ^ 3 := by positivity
    have h1 : (2 * K₁ + 2 * B + 1) * u ^ 3 ≤ u * u ^ 3 := mul_le_mul_of_nonneg_right hMu_a hu3
    have h2 : 2 * B * u ^ 2 ≤ 2 * B * u ^ 3 := mul_le_mul_of_nonneg_left hu23 (by positivity)
    have e1 : u * u ^ 3 = u ^ 4 := by ring
    linarith
  have ht₀s : t₀ < s := by
    have h1 : u ^ 2 < u ^ 4 := by
      have : 1 < u := lt_of_lt_of_le (by linarith) hMu_a
      exact pow_lt_pow_right₀ this (by norm_num)
    rw [ht₀, hs]
    have := mul_lt_mul_of_pos_left h1 (by positivity : 0 < q ^ 2)
    calc (q * u) ^ 2 = q ^ 2 * u ^ 2 := by ring
      _ < q ^ 2 * u ^ 4 := this
      _ = (q * u ^ 2) ^ 2 := by ring
  have hq2t : q ^ 2 ≤ t₀ := by
    rw [ht₀, mul_pow]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hu1)
  -- the spectrum of `A`
  set a := specOf A with ha_def
  set L := LpW a with hL_def
  have ha2 : ∀ i, |a i| ≤ τ⁻¹ - 2 := fun i => by linarith [ha i]
  have hL : |L| ≤ τ⁻¹ - 1 := by
    have := abs_LpW_le hN1 ha
    linarith
  have hsqrt := hsq N hNs a ha2 hSB
  -- the law events
  set law : ℂ → Set Ω := fun z =>
    {ω | ‖mNW A (W ω) z - mW a z‖ ≤ (N : ℝ) ^ (δ / 2) * (CΦ / (N * z.im))} with hlaw_def
  have hlaw : ∀ z ∈ edgeConeW τ N a c₁ κ, HighProbAt N 3 (law z) := by
    intro z hz
    have h := hav z hz
    unfold ODomAt DomAt at h
    unfold HighProbAt
    convert h using 2
    ext ω
    simp only [law, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    exact Iff.rfl
  have hlawIm : ∀ z : ℂ, 0 < z.im → ∀ ω ∈ law z,
      |(mNW A (W ω) z).im - (mW a z).im| ≤ u ^ 2 * B / (N * z.im) := by
    intro z hz ω hω
    have h1 : ‖mNW A (W ω) z - mW a z‖ ≤ (N : ℝ) ^ (δ / 2) * (CΦ / (N * z.im)) := hω
    have h2 := Complex.abs_im_le_norm (mNW A (W ω) z - mW a z)
    rw [Complex.sub_im] at h2
    have hNz : 0 < (N : ℝ) * z.im := mul_pos hNr0 hz
    have h3 : (N : ℝ) ^ (δ / 2) * (CΦ / (N * z.im)) ≤ u ^ 2 * B / (N * z.im) := by
      rw [hu2, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (le_abs_self CΦ) hNz.le) (by positivity)
    linarith
  -- the rigidity event
  set R : Set Ω := {ω | max (sortedEig (W ω + A) 1 - L) 0 ≤
    (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (-2 / 3 : ℝ)} with hR_def
  have hR : HighProbAt N 3 R := by
    have h := hrig
    unfold RigidExtremesWAt RigidExtremesAt DomAt at h
    unfold HighProbAt
    convert h.1 using 2
    ext ω
    simp only [R, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    exact Iff.rfl
  -- the points
  set η₁ := s / (2 * κ) with hη₁
  have hη₁0 : 0 < η₁ := by positivity
  set E₃ := L - s / 2 with hE₃
  have hκη₁ : κ * η₁ = s / 2 := by rw [hη₁]; field_simp
  have hE₃L : |E₃ - L| = s / 2 := by
    rw [hE₃, show L - s / 2 - L = -(s / 2) by ring, abs_neg, abs_of_pos (by positivity)]
  have hη₁q : q ^ 2 ≤ η₁ := by
    rw [hη₁, le_div_iff₀ (by positivity), hs]
    have : q ^ 2 * (2 * κ) ≤ q ^ 2 * u ^ 4 := mul_le_mul_of_nonneg_left hMu_c (by positivity)
    calc q ^ 2 * (2 * κ) ≤ q ^ 2 * u ^ 4 := this
      _ = (q * u ^ 2) ^ 2 := by ring
  have hη₁s : η₁ ≤ s / 2 := by
    rw [← hκη₁]
    exact le_mul_of_one_le_left hη₁0.le (by linarith)
  have hz₁ : ((E₃ : ℂ) + η₁ * Complex.I) ∈ edgeConeW τ N a c₁ κ :=
    aux_mem_cone hτ hτ4 hN1 hL hc₁1 (by rw [hE₃L]; linarith) (by rw [hE₃L, hκη₁])
      (hp ▸ hη₁q) (by linarith)
  have hz₂eq : ((E₃ : ℂ) + κ * η₁ * Complex.I) = ((E₃ : ℂ) + ((κ * η₁ : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have hz₂ : ((E₃ : ℂ) + κ * η₁ * Complex.I) ∈ edgeConeW τ N a c₁ κ := by
    rw [hz₂eq]
    refine aux_mem_cone hτ hτ4 hN1 hL hc₁1 (by rw [hE₃L]; linarith) ?_ ?_ (by linarith)
    · rw [hE₃L, hκη₁]
      exact le_mul_of_one_le_left (by positivity) (by linarith)
    · rw [hp]; linarith
  set g : ℕ → ℂ := fun n =>
    ((L - n * t₀ / 2 : ℝ) : ℂ) + (((n + 2) * t₀ / 2 : ℝ) : ℂ) * Complex.I with hg_def
  set M := ⌊(c₁ / 8) / t₀⌋₊ + 1 with hM
  have hgrid : ∀ n, n < M → (n : ℝ) * t₀ ≤ c₁ / 8 := by
    intro n hn
    have h1 : n ≤ ⌊(c₁ / 8) / t₀⌋₊ := by omega
    have h2 : (n : ℝ) ≤ (c₁ / 8) / t₀ :=
      le_trans (Nat.cast_le.2 h1) (Nat.floor_le (by positivity))
    rwa [le_div_iff₀ ht₀0] at h2
  have hgE : ∀ n : ℕ, |(L - n * t₀ / 2) - L| = n * t₀ / 2 := by
    intro n
    rw [show L - n * t₀ / 2 - L = -(n * t₀ / 2) by ring, abs_neg, abs_of_nonneg (by positivity)]
  have hgcone : ∀ n, n < M → g n ∈ edgeConeW τ N a c₁ κ := by
    intro n hn
    have h1 := hgrid n hn
    refine aux_mem_cone hτ hτ4 hN1 hL hc₁1 (by rw [hgE]; linarith) ?_ ?_ ?_
    · rw [hgE]
      have : (n : ℝ) * t₀ / 2 ≤ (n + 2) * t₀ / 2 := by linarith
      exact this.trans (le_mul_of_one_le_left (by positivity) (by linarith))
    · rw [hp]
      have : (0 : ℝ) ≤ n * t₀ := by positivity
      linarith
    · linarith
  -- the family of events
  set F : Fin 3 ⊕ ℕ → Set Ω :=
    Sum.elim ![R, law ((E₃ : ℂ) + η₁ * Complex.I), law ((E₃ : ℂ) + κ * η₁ * Complex.I)]
      (fun n => law (g n)) with hF
  set S : Finset (Fin 3 ⊕ ℕ) := (Finset.univ : Finset (Fin 3)).disjSum (Finset.range M) with hS
  have hcard : ((S.card : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [hS, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin, Finset.card_range,
      Real.rpow_two]
    have hM1 : ⌊(c₁ / 8) / t₀⌋₊ ≤ N := by
      refine Nat.floor_le_of_le ?_
      rw [div_le_iff₀ ht₀0]
      have : (1 : ℝ) ≤ N * t₀ := by
        rw [← hNq]
        have : q ^ 3 ≤ t₀ := le_trans (pow_le_pow_of_le_one hq0.le hq1 (by norm_num)) hq2t
        exact mul_le_mul_of_nonneg_left this hNr0.le
      linarith
    have hNN : 3 * N ≤ N ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right N hN3
    have : 3 + M ≤ N ^ 2 := by rw [hM]; omega
    exact_mod_cast this
  have hall : ∀ i ∈ S, HighProbAt N (1 + 2) (F i) := by
    rw [show (1 : ℝ) + 2 = 3 by norm_num]
    rintro (j | n) hi
    · fin_cases j
      · exact hR
      · exact hlaw _ hz₁
      · exact hlaw _ hz₂
    · rw [Finset.inr_mem_disjSum, Finset.mem_range] at hi
      exact hlaw _ (hgcone n hi)
  have hinter := HighProbAt.biInter S hN1 hcard hall
  unfold HighProbAt at hinter ⊢
  refine le_trans (measure_mono ?_) hinter
  rw [Set.compl_subset_compl]
  intro ω hω
  have hmem : ∀ i ∈ S, ω ∈ F i := Set.mem_iInter₂.1 hω
  have hωR : ω ∈ R := hmem (Sum.inl 0) (by simp [hS])
  have hω1 : ω ∈ law ((E₃ : ℂ) + η₁ * Complex.I) := hmem (Sum.inl 1) (by simp [hS])
  have hω2 : ω ∈ law ((E₃ : ℂ) + κ * η₁ * Complex.I) := hmem (Sum.inl 2) (by simp [hS])
  have hωg : ∀ n, n < M → ω ∈ law (g n) := fun n hn =>
    hmem (Sum.inr n) (by rw [hS, Finset.inr_mem_disjSum, Finset.mem_range]; exact hn)
  -- the deterministic part
  have hH : (W ω + A).IsHermitian := (hW ω).add hA
  have hlam : ∀ k, specOf (W ω + A) k ≤ L + t₀ := by
    intro k
    have h1 : max (sortedEig (W ω + A) 1 - L) 0 ≤ (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) :=
      hωR
    rw [hu2, hp] at h1
    have h2 := aux_spec_le_sortedEig hN1 hH k
    have h3 := le_trans (le_max_left _ _) h1
    have e : (q * u) ^ 2 = u ^ 2 * q ^ 2 := by ring
    rw [ht₀, e]
    linarith
  have hsq' : ∀ z : ℂ, 0 < z.im → |z.re - L| + z.im ≤ c₁ → z.re ≤ L →
      K₁⁻¹ * √(L - z.re + z.im) ≤ (mW a z).im ∧ (mW a z).im ≤ K₁ * √(L - z.re + z.im) := by
    intro z hz hzc hzre
    have hn : ‖z - (L : ℂ)‖ ≤ cs := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
        abs_of_pos hz]
      linarith
    obtain ⟨h1, h2⟩ := (hsqrt z hz hn).1 hzre
    exact ⟨le_trans (mul_le_mul_of_nonneg_right hKinv (Real.sqrt_nonneg _)) h1,
      le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩
  refine aux_regime_det hA (hW ω) hN1 hq0 hu1 hNq hu4 hspow hK₁1 hB0 hMu_b h7 hss ht₀s hsq' hlam
    ?_ ?_ ?_
  · have h1im : ((E₃ : ℂ) + η₁ * Complex.I).im = η₁ := by simp
    have h := hlawIm _ (by rw [h1im]; exact hη₁0) ω hω1
    rw [h1im] at h
    exact h
  · have h2im : ((E₃ : ℂ) + κ * η₁ * Complex.I).im = κ * η₁ := by simp
    have h := hlawIm _ (by rw [h2im]; positivity) ω hω2
    rw [h2im] at h
    exact h
  · intro n hn
    have hgim : (g n).im = (n + 2) * t₀ / 2 := by simp [g]
    have h := hlawIm (g n) (by rw [hgim]; positivity) ω (hωg n ?_)
    · rw [hgim] at h
      exact h
    · rw [hM]
      have : n ≤ ⌊(c₁ / 8) / t₀⌋₊ := Nat.le_floor (by rw [le_div_iff₀ ht₀0]; exact hn)
      omega

/-- The spectral form of `Im N⁻¹ tr G^W` at `N = 2` for `A = aEx 2`, `W = 0`, `z = i`. -/
example : (mNW (aEx 2) 0 Complex.I).im =
    ((2 : ℕ) : ℝ)⁻¹ * ∑ k, Complex.I.im /
      ((specOf (0 + aEx 2) k - Complex.I.re) ^ 2 + Complex.I.im ^ 2) :=
  im_mNW_eq (aEx_isHermitian 2) Matrix.isHermitian_zero (by simp)

/-- The two counts at `N = 2` for `A = aEx 2`, `W = 0`, `E = 0`, `r = η = 1`, `κ = 2`. -/
example : (((Finset.univ.filter fun k => |specOf (0 + aEx 2) k - 0| ≤ 1).card : ℕ) : ℝ) ≤
      2 * (2 : ℕ) * 1 * (mNW (aEx 2) 0 (0 + (1 : ℝ) * Complex.I)).im ∧
    ((2 : ℕ) : ℝ) * 1 * ((mNW (aEx 2) 0 (0 + (1 : ℝ) * Complex.I)).im -
        2 / 2 * (mNW (aEx 2) 0 (0 + (2 : ℝ) * 1 * Complex.I)).im) ≤
      (((Finset.univ.filter fun k =>
        |specOf (0 + aEx 2) k - 0| < Real.sqrt (2 ^ 2 - 2) * 1).card : ℕ) : ℝ) :=
  ⟨card_eig_near_le (aEx_isHermitian 2) Matrix.isHermitian_zero 0 one_pos,
    card_eig_near_ge (aEx_isHermitian 2) Matrix.isHermitian_zero 0 one_pos le_rfl⟩

#print axioms im_mNW_eq
#print axioms card_eig_near_le
#print axioms card_eig_near_ge
#print axioms edgeRegime_wig

end Anisotropic
