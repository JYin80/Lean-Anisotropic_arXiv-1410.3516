import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Rigidity.Defs
import Anisotropic.Rigidity.Exclusion
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.EdgeSqrt
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # From the bound outside the spectrum to rigid extremes -/

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

/-- `N⁻¹ tr (W + A − z)⁻¹` is the Stieltjes transform of the eigenvalues of the symmetric
`W + A`, for `Im z > 0`. -/
private lemma aux_mNW_eq {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : mNW A Wm z = empStieltjes (specOf (Wm + A)) z := by
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
  unfold mNW GW empStieltjes
  rw [hinv, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.trace_diagonal,
    specOf_eq hH]

/-- The deterministic core of the exclusion argument of §10 (from (tur1)): an eigenvalue in
`[E − η, E + η]` forces `N⁻¹ ((n+1)η²)^{−n} ≤ B + (∑ₖ |C_{n,k}|) δ η^{−2n}` whenever
`|∑ₖ C_{n,k} η^{1−2n} Im m(z_k)| ≤ B` and `|s(z_k) − m(z_k)| ≤ δ/η` at the nodes
`z_k = E + i√k η`, `s` the Stieltjes transform of the eigenvalues. -/
private lemma aux_tur_core {N n : ℕ} (hn : 1 ≤ n) (lam : Fin N → ℝ) (mf : ℂ → ℂ) {E η : ℝ}
    (hη : 0 < η) {i : Fin N} (hi : |lam i - E| ≤ η) {B δ : ℝ}
    (hdet : |∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
      (mf ⟨E, √(k : ℝ) * η⟩).im| ≤ B)
    (hfl : ∀ k ∈ Finset.Icc 1 n,
      ‖empStieltjes lam ⟨E, √(k : ℝ) * η⟩ - mf ⟨E, √(k : ℝ) * η⟩‖ ≤ δ / η) :
    (N : ℝ)⁻¹ * ((((n : ℝ) + 1) * η ^ 2) ^ n)⁻¹ ≤
      B + (∑ k ∈ Finset.Icc 1 n, |turC n k|) * δ * ((η ^ 2) ^ n)⁻¹ := by
  have ht := tur1 n hn lam E η hη
  have hη2 : 0 < η ^ 2 := by positivity
  have hfac : ∀ j, ∀ k ∈ Finset.Icc 1 n, 0 ≤ ((lam j - E) ^ 2 + k * η ^ 2)⁻¹ := fun j k _ =>
    inv_nonneg.2 (by positivity)
  have hlow : (N : ℝ)⁻¹ * ((((n : ℝ) + 1) * η ^ 2) ^ n)⁻¹ ≤
      (N : ℝ)⁻¹ * ∑ j, ∏ k ∈ Finset.Icc 1 n, ((lam j - E) ^ 2 + k * η ^ 2)⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∏ k ∈ Finset.Icc 1 n,
      ((lam j - E) ^ 2 + k * η ^ 2)⁻¹) (fun j _ => Finset.prod_nonneg (hfac j))
      (Finset.mem_univ i))
    have hc : ∏ _k ∈ Finset.Icc 1 n, (((n : ℝ) + 1) * η ^ 2)⁻¹ =
        ((((n : ℝ) + 1) * η ^ 2) ^ n)⁻¹ := by
      rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, inv_pow]
    rw [← hc]
    refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k hk => ?_)
    have hk := Finset.mem_Icc.1 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.2
    have hsq : (lam i - E) ^ 2 ≤ η ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi 2
    refine inv_anti₀ (by positivity) ?_
    nlinarith
  have hz : ∀ k : ℕ, η ^ (1 - 2 * (n : ℤ)) * (δ / η) = δ * ((η ^ 2) ^ n)⁻¹ := by
    intro _
    rw [zpow_sub₀ hη.ne', zpow_one, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul]
    field_simp
  have hzp : 0 < η ^ (1 - 2 * (n : ℤ)) := zpow_pos hη _
  have hsplit : ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
      (empStieltjes lam ⟨E, √(k : ℝ) * η⟩).im =
      ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) * (mf ⟨E, √(k : ℝ) * η⟩).im +
      ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
        (empStieltjes lam ⟨E, √(k : ℝ) * η⟩ - mf ⟨E, √(k : ℝ) * η⟩).im := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.sub_im]
    ring
  have hfl' : ∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
      (empStieltjes lam ⟨E, √(k : ℝ) * η⟩ - mf ⟨E, √(k : ℝ) * η⟩).im ≤
      (∑ k ∈ Finset.Icc 1 n, |turC n k|) * δ * ((η ^ 2) ^ n)⁻¹ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    set w := empStieltjes lam ⟨E, √(k : ℝ) * η⟩ - mf ⟨E, √(k : ℝ) * η⟩
    have h1 : turC n k * η ^ (1 - 2 * (n : ℤ)) * w.im ≤
        |turC n k| * η ^ (1 - 2 * (n : ℤ)) * |w.im| := by
      rw [mul_assoc, mul_assoc]
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hzp]
    have h2 : |w.im| ≤ δ / η := (Complex.abs_im_le_norm w).trans (hfl k hk)
    calc turC n k * η ^ (1 - 2 * (n : ℤ)) * w.im ≤
          |turC n k| * η ^ (1 - 2 * (n : ℤ)) * |w.im| := h1
      _ ≤ |turC n k| * η ^ (1 - 2 * (n : ℤ)) * (δ / η) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = |turC n k| * δ * ((η ^ 2) ^ n)⁻¹ := by rw [mul_assoc, hz k]; ring
  rw [ht, hsplit] at hlow
  linarith [le_abs_self (∑ k ∈ Finset.Icc 1 n, turC n k * η ^ (1 - 2 * (n : ℤ)) *
    (mf ⟨E, √(k : ℝ) * η⟩).im)]

/-- The exponent bookkeeping of the exclusion (§10, with `η = N^{−τ_S} κ`, `κ ≤ τ_S⁻¹`): under
`2K(n+1)ⁿ N (N^{−τ_S}τ_S⁻¹)^{2n} < 1` and `2S(n+1)ⁿ δN < 1`, the upper bound of the core
inequality is strictly below the lower bound. -/
private lemma aux_arith {N : ℝ} {n : ℕ} (hN : 0 < N) {κ τS p K S δ : ℝ} (hκ : 0 < κ)
    (hκS : κ ≤ τS⁻¹) (hτS : 0 < τS) (hτS1 : τS ≤ 1) (hp : 0 < p) (hK : 0 < K)
    (C1 : 2 * K * ((n : ℝ) + 1) ^ n * N * ((p * τS⁻¹) ^ 2) ^ n < 1)
    (C2 : 2 * S * ((n : ℝ) + 1) ^ n * (δ * N) < 1) :
    K * min κ 1 ^ (1 - 2 * (n : ℤ)) + S * δ * (((p * κ) ^ 2) ^ n)⁻¹ <
      N⁻¹ * ((((n : ℝ) + 1) * (p * κ) ^ 2) ^ n)⁻¹ := by
  set m := min κ 1 with hm
  have hm0 : 0 < m := lt_min hκ one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hτS1' : 1 ≤ τS⁻¹ := one_le_inv₀ hτS |>.2 hτS1
  have hκm : κ ≤ τS⁻¹ * m := by
    rcases le_total κ 1 with h | h
    · rw [hm, min_eq_left h]; nlinarith
    · rw [hm, min_eq_right h, mul_one]; exact hκS
  set q := p * τS⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hηq : p * κ ≤ q * m := by
    rw [hq, mul_assoc]; exact mul_le_mul_of_nonneg_left hκm hp.le
  set P := ((p * κ) ^ 2) ^ n with hP
  have hP0 : 0 < P := by positivity
  have hPle : P ≤ (q ^ 2) ^ n * (m ^ 2) ^ n := by
    rw [hP, ← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    exact pow_le_pow_left₀ (by positivity) hηq 2
  have hzm : m ^ (1 - 2 * (n : ℤ)) ≤ ((m ^ 2) ^ n)⁻¹ := by
    rw [zpow_sub₀ hm0.ne', zpow_one, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul, div_eq_mul_inv]
    have : 0 < ((m ^ 2) ^ n)⁻¹ := by positivity
    nlinarith
  have hmn : 0 < (m ^ 2) ^ n := by positivity
  have hqn : 0 < (q ^ 2) ^ n := by positivity
  have h1 : ((m ^ 2) ^ n)⁻¹ ≤ (q ^ 2) ^ n * P⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hmn]
    rw [show (q ^ 2) ^ n * P⁻¹ * (m ^ 2) ^ n = ((q ^ 2) ^ n * (m ^ 2) ^ n) / P by
      field_simp]
    rw [le_div_iff₀ hP0, one_mul]
    exact hPle
  have hn1 : 0 < ((n : ℝ) + 1) ^ n := by positivity
  have hR : N⁻¹ * ((((n : ℝ) + 1) * (p * κ) ^ 2) ^ n)⁻¹ = N⁻¹ * (((n : ℝ) + 1) ^ n)⁻¹ * P⁻¹ := by
    rw [mul_pow, mul_inv]; ring
  rw [hR]
  set R := N⁻¹ * (((n : ℝ) + 1) ^ n)⁻¹ * P⁻¹ with hRdef
  have hR0 : 0 < R := by positivity
  have hA : K * ((q ^ 2) ^ n * P⁻¹) = (2 * K * ((n : ℝ) + 1) ^ n * N * (q ^ 2) ^ n) * (R / 2) := by
    rw [hRdef]; field_simp
  have hB : S * δ * P⁻¹ = (2 * S * ((n : ℝ) + 1) ^ n * (δ * N)) * (R / 2) := by
    rw [hRdef]; field_simp
  have e1 : K * m ^ (1 - 2 * (n : ℤ)) ≤ K * ((q ^ 2) ^ n * P⁻¹) :=
    mul_le_mul_of_nonneg_left (hzm.trans h1) hK.le
  have e2 : (2 * K * ((n : ℝ) + 1) ^ n * N * (q ^ 2) ^ n) * (R / 2) < R / 2 := by
    have := mul_lt_mul_of_pos_right C1 (half_pos hR0)
    linarith
  have e3 : (2 * S * ((n : ℝ) + 1) ^ n * (δ * N)) * (R / 2) < R / 2 := by
    have := mul_lt_mul_of_pos_right C2 (half_pos hR0)
    linarith
  linarith

/-- One side of the exclusion of §10 at fixed `ω`, on the grid `κ_j = u + j h`, `η_j = p κ_j`,
`E_j = L + s κ_j` (`s = ±1`): if every eigenvalue satisfies `s(λᵢ − L) ≤ τ_S⁻¹`, and the
counterpart of (tur2) and the bound `|s − m| ≤ δ/η_j` hold at the nodes `E_j + i√k η_j` of every
grid point with `j < N`, `κ_j ≤ τ_S⁻¹`, then `s(λᵢ − L) < u` for every eigenvalue. -/
private lemma aux_side {N n : ℕ} (hn : 1 ≤ n) (lam : Fin N → ℝ) (mf : ℂ → ℂ)
    {L s τS K δ u h p : ℝ} (hs : s * s = 1) (hτS : 0 < τS) (hτS1 : τS ≤ 1) (hK : 0 < K)
    (hu : 0 < u) (hh : 0 < h) (hp : 0 < p) (hpu : p * u = h)
    (hrange : ∀ i, s * (lam i - L) ≤ τS⁻¹) (hjN : τS⁻¹ / h < N)
    (C1 : 2 * K * ((n : ℝ) + 1) ^ n * N * ((p * τS⁻¹) ^ 2) ^ n < 1)
    (C2 : 2 * (∑ k ∈ Finset.Icc 1 n, |turC n k|) * ((n : ℝ) + 1) ^ n * (δ * N) < 1)
    (hdet : ∀ j : ℕ, j < N → u + j * h ≤ τS⁻¹ →
      |∑ k ∈ Finset.Icc 1 n, turC n k * (p * (u + j * h)) ^ (1 - 2 * (n : ℤ)) *
        (mf ⟨L + s * (u + j * h), √(k : ℝ) * (p * (u + j * h))⟩).im| ≤
        K * min (u + j * h) 1 ^ (1 - 2 * (n : ℤ)))
    (hfl : ∀ j : ℕ, j < N → u + j * h ≤ τS⁻¹ → ∀ k ∈ Finset.Icc 1 n,
      ‖empStieltjes lam ⟨L + s * (u + j * h), √(k : ℝ) * (p * (u + j * h))⟩ -
        mf ⟨L + s * (u + j * h), √(k : ℝ) * (p * (u + j * h))⟩‖ ≤ δ / (p * (u + j * h))) :
    ∀ i, s * (lam i - L) < u := by
  intro i
  by_contra hcon
  push Not at hcon
  set d := s * (lam i - L) with hd
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hjN
  have hq0 : 0 ≤ (d - u) / h := div_nonneg (by linarith) hh.le
  set j := ⌊(d - u) / h⌋₊ with hjdef
  have hj0 : (j : ℝ) ≤ (d - u) / h := Nat.floor_le hq0
  have hj1 : (d - u) / h < j + 1 := Nat.lt_floor_add_one _
  set κ := u + j * h with hκ
  have hκd : κ ≤ d := by
    have := (le_div_iff₀ hh).1 hj0
    linarith
  have hdκ : d < κ + h := by
    have := (div_lt_iff₀ hh).1 hj1
    linarith
  have hκS : κ ≤ τS⁻¹ := hκd.trans (hrange i)
  have hκ0 : 0 < κ := by
    have : (0 : ℝ) ≤ j * h := by positivity
    linarith
  have hjN' : j < N := by
    have h1 : (j : ℝ) ≤ τS⁻¹ / h := by
      refine hj0.trans ?_
      exact div_le_div_of_nonneg_right (by linarith [hrange i]) hh.le
    exact_mod_cast h1.trans_lt hjN
  have hη : h ≤ p * κ := by
    rw [← hpu]
    have hj : (0 : ℝ) ≤ j * h := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hp.le
  have hsabs : |s| = 1 := by
    have h1 : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
    nlinarith [abs_nonneg s]
  have hi : |lam i - (L + s * κ)| ≤ p * κ := by
    have e : lam i - (L + s * κ) = s * (d - κ) := by
      rw [hd]
      have : s * (s * (lam i - L)) = lam i - L := by rw [← mul_assoc, hs, one_mul]
      linear_combination -this
    rw [e, abs_mul, hsabs, one_mul, abs_of_nonneg (by linarith)]
    linarith
  have hcore := aux_tur_core hn lam mf (by positivity) hi (hdet j hjN' hκS) (hfl j hjN' hκS)
  have harith := aux_arith hNpos hκ0 hκS hτS hτS1 hp hK C1 C2
  linarith

/-- The large-`N` conditions of the exclusion: for `n τ_S ≥ 2`, eventually
`2K(n+1)ⁿ N (N^{−τ_S}τ_S⁻¹)^{2n} < 1`, `2S(n+1)ⁿ N^{−c/2} < 1`, `n (N^{−τ_S}τ_S⁻¹)² ≤ c_T²`,
`√n N^{−τ_S} ≤ N^{−τ_S/2}` and `τ_S⁻¹ N^{2/3} < N`. -/
private lemma aux_eventually {τS c K S cT : ℝ} {n : ℕ} (hτS : 0 < τS) (hc : 0 < c) (hK : 0 < K)
    (hS : 0 ≤ S) (hcT : 0 < cT) (hn : 1 ≤ n) (hnτ : 2 ≤ (n : ℝ) * τS) :
    ∀ᶠ N : ℕ in atTop,
      2 * K * ((n : ℝ) + 1) ^ n * N * ((((N : ℝ) ^ (-τS)) * τS⁻¹) ^ 2) ^ n < 1 ∧
      2 * S * ((n : ℝ) + 1) ^ n * ((N : ℝ) ^ (c / 2) * (N : ℝ) ^ (-c) / N * N) < 1 ∧
      (n : ℝ) * ((N : ℝ) ^ (-τS) * τS⁻¹) ^ 2 ≤ cT ^ 2 ∧
      √(n : ℝ) * (N : ℝ) ^ (-τS) ≤ (N : ℝ) ^ (-τS / 2) ∧
      τS⁻¹ / (N : ℝ) ^ (-2 / 3 : ℝ) < N := by
  have hlim : ∀ {q : ℝ}, 0 < q → Tendsto (fun N : ℕ => (N : ℝ) ^ (-q)) atTop (𝓝 0) :=
    fun hq => (tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  set A1 := 2 * K * ((n : ℝ) + 1) ^ n * (τS⁻¹ ^ 2) ^ n with hA1
  have hA1p : 0 < A1 := by positivity
  set A2 := 2 * S * ((n : ℝ) + 1) ^ n with hA2
  have hA2p : 0 ≤ A2 := by positivity
  have e1 := (hlim (show 0 < 2 * n * τS - 1 by linarith)).eventually
    (gt_mem_nhds (show 0 < A1⁻¹ by positivity))
  have e2 := (hlim (show 0 < c / 2 by positivity)).eventually
    (gt_mem_nhds (show 0 < (A2 + 1)⁻¹ by positivity))
  have e3 := (hlim hτS).eventually (gt_mem_nhds (show 0 < cT * τS / √(n : ℝ) by positivity))
  have e4 := (hlim (show 0 < τS / 2 by positivity)).eventually
    (gt_mem_nhds (show 0 < (√(n : ℝ))⁻¹ by positivity))
  have e5 := (hlim (show (0 : ℝ) < 1 / 3 by norm_num)).eventually (gt_mem_nhds hτS)
  filter_upwards [e1, e2, e3, e4, e5, eventually_gt_atTop 0] with N h1 h2 h3 h4 h5 hN0
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : (N : ℝ) * ((((N : ℝ) ^ (-τS)) * τS⁻¹) ^ 2) ^ n =
        (τS⁻¹ ^ 2) ^ n * (N : ℝ) ^ (-(2 * n * τS - 1)) := by
      have h2n : (((N : ℝ) ^ (-τS)) ^ 2) ^ n = (N : ℝ) ^ (-τS * ((2 * n : ℕ) : ℝ)) := by
        rw [Real.rpow_mul_natCast hN.le, pow_mul]
      have hadd : (N : ℝ) ^ (-(2 * n * τS - 1)) =
          (N : ℝ) * (N : ℝ) ^ (-τS * ((2 * n : ℕ) : ℝ)) := by
        rw [show -(2 * n * τS - 1) = 1 + -τS * ((2 * n : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_add hN, Real.rpow_one]
      rw [mul_pow, mul_pow, h2n, hadd]
      ring
    have h1' : (N : ℝ) ^ (-(2 * n * τS - 1)) < A1⁻¹ := h1
    calc 2 * K * ((n : ℝ) + 1) ^ n * N * ((((N : ℝ) ^ (-τS)) * τS⁻¹) ^ 2) ^ n
        = A1 * (N : ℝ) ^ (-(2 * n * τS - 1)) := by
          rw [mul_assoc (2 * K * ((n : ℝ) + 1) ^ n), e, hA1]; ring
      _ < A1 * A1⁻¹ := mul_lt_mul_of_pos_left h1' hA1p
      _ = 1 := mul_inv_cancel₀ hA1p.ne'
  · have e : (N : ℝ) ^ (c / 2) * (N : ℝ) ^ (-c) / N * N = (N : ℝ) ^ (-(c / 2)) := by
      rw [div_mul_cancel₀ _ hN.ne', ← Real.rpow_add hN]
      ring_nf
    have h2' : (N : ℝ) ^ (-(c / 2)) < (A2 + 1)⁻¹ := h2
    rw [e]
    have hy : 0 ≤ (N : ℝ) ^ (-(c / 2)) := by positivity
    have : (A2 + 1) * (N : ℝ) ^ (-(c / 2)) < 1 := by
      calc (A2 + 1) * (N : ℝ) ^ (-(c / 2)) < (A2 + 1) * (A2 + 1)⁻¹ :=
            mul_lt_mul_of_pos_left h2' (by linarith)
        _ = 1 := mul_inv_cancel₀ (by linarith)
    nlinarith
  · have h3' : (N : ℝ) ^ (-τS) < cT * τS / √(n : ℝ) := h3
    have hb : (N : ℝ) ^ (-τS) * τS⁻¹ ≤ cT / √(n : ℝ) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hτS]
      calc (N : ℝ) ^ (-τS) ≤ cT * τS / √(n : ℝ) := h3'.le
        _ = cT / √(n : ℝ) * τS := by ring
    have hb0 : 0 ≤ (N : ℝ) ^ (-τS) * τS⁻¹ := by positivity
    have hsq := pow_le_pow_left₀ hb0 hb 2
    rw [div_pow, Real.sq_sqrt hn0.le] at hsq
    calc (n : ℝ) * ((N : ℝ) ^ (-τS) * τS⁻¹) ^ 2 ≤ n * (cT ^ 2 / n) :=
          mul_le_mul_of_nonneg_left hsq hn0.le
      _ = cT ^ 2 := by field_simp
  · have h4' : (N : ℝ) ^ (-(τS / 2)) < (√(n : ℝ))⁻¹ := h4
    have e : (N : ℝ) ^ (-τS) = (N : ℝ) ^ (-τS / 2) * (N : ℝ) ^ (-τS / 2) := by
      rw [← Real.rpow_add hN]; ring_nf
    rw [e, ← mul_assoc]
    have hx : 0 ≤ (N : ℝ) ^ (-τS / 2) := by positivity
    have : √(n : ℝ) * (N : ℝ) ^ (-τS / 2) ≤ 1 := by
      rw [neg_div]
      calc √(n : ℝ) * (N : ℝ) ^ (-(τS / 2)) ≤ √(n : ℝ) * (√(n : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left h4'.le hsn.le
        _ = 1 := mul_inv_cancel₀ hsn.ne'
    nlinarith
  · have h5' : (N : ℝ) ^ (-(1 / 3 : ℝ)) < τS := h5
    have hh : 0 < (N : ℝ) ^ (-2 / 3 : ℝ) := by positivity
    rw [div_lt_iff₀ hh]
    have e : (N : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_one_add' hN.le (by norm_num)]; norm_num
    have e2 : (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hN]; norm_num
    rw [e]
    have hpos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
    rw [inv_lt_iff_one_lt_mul₀ hτS]
    nlinarith

/-- `g(x) ≥ x` to the right of the spectrum and `g(x) ≤ x` to its left; with `x₊ > maxᵢ aᵢ` and
`x₋ < minᵢ aᵢ` this gives `−R ≤ L₊`, `L₋ ≤ R` and `L₋ ≤ L₊` when `|aᵢ| ≤ R` (§12.1). -/
private lemma aux_L_facts {N : ℕ} (hN : 1 ≤ N) {a : Fin N → ℝ} {τ R : ℝ} (hτ : 0 < τ)
    (hgap : (⨆ i, a i) + τ / 4 ≤ xpW a ∧ xmW a ≤ (⨅ i, a i) - τ / 4) (hR : ∀ i, |a i| ≤ R) :
    -R ≤ LpW a ∧ LmW a ≤ R ∧ LmW a ≤ LpW a := by
  have hle : ∀ i, a i ≤ ⨆ i, a i := fun i => le_ciSup (Set.finite_range a).bddAbove i
  have hge : ∀ i, (⨅ i, a i) ≤ a i := fun i => ciInf_le (Set.finite_range a).bddBelow i
  have hp : ∀ i, a i < xpW a := fun i => by linarith [hle i, hgap.1]
  have hm : ∀ i, xmW a < a i := fun i => by linarith [hge i, hgap.2]
  have hgp : xpW a ≤ LpW a := by
    unfold LpW gW
    have : ∑ i, (a i - xpW a)⁻¹ ≤ 0 :=
      Finset.sum_nonpos fun i _ => inv_nonpos.2 (by linarith [hp i])
    have : (N : ℝ)⁻¹ * ∑ i, (a i - xpW a)⁻¹ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    linarith
  have hgm : LmW a ≤ xmW a := by
    unfold LmW gW
    have : 0 ≤ ∑ i, (a i - xmW a)⁻¹ :=
      Finset.sum_nonneg fun i _ => inv_nonneg.2 (by linarith [hm i])
    have : 0 ≤ (N : ℝ)⁻¹ * ∑ i, (a i - xmW a)⁻¹ := mul_nonneg (by positivity) this
    linarith
  set i₀ : Fin N := ⟨0, hN⟩
  have h1 := abs_le.1 (hR i₀)
  exact ⟨by linarith [hp i₀], by linarith [hm i₀], by linarith [hp i₀, hm i₀]⟩

/-- The standing bound of §12.1 on `𝐃^W(τ, N)` is invariant under `a ↦ −a` (reflection
`m^W_{−a}(−z̄) = −conj m^W_a(z)`). -/
private lemma aux_sb_neg {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} {a : Fin N → ℝ}
    (h : StandingBoundW τ a (domW τ N)) : StandingBoundW τ (-a) (domW τ N) := by
  intro z hz i
  set w := -(starRingEnd ℂ) z with hw
  have hwd : w ∈ domW τ N := by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hw, abs_neg] <;> assumption
  have hzw : z = -(starRingEnd ℂ) w := by simp [hw]
  have hmw := mW_neg hN a hwd.1
  rw [hzw, hmw]
  refine (h w hwd i).trans (le_of_eq ?_)
  rw [← Complex.norm_conj, ← norm_neg]
  congr 1
  simp only [map_add, map_sub, map_neg, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg]
  ring

/-- `Im m^W_{−a}(−x + iy) = Im m^W_a(x + iy)` for `y > 0`. -/
private lemma aux_im_neg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {x y : ℝ} (hy : 0 < y) :
    (mW (-a) ⟨-x, y⟩).im = (mW a ⟨x, y⟩).im := by
  have e : (⟨-x, y⟩ : ℂ) = -(starRingEnd ℂ) ⟨x, y⟩ := Complex.ext (by simp) (by simp)
  rw [e, mW_neg hN a (by simpa using hy)]
  simp

/-- `κ(L₊ + κ) = κ` and `κ(L₋ − κ) = κ` for `κ ≥ 0` when `L₋ ≤ L₊`. -/
private lemma aux_kappa {N : ℕ} {a : Fin N → ℝ} (hL : LmW a ≤ LpW a) {κ : ℝ} (hκ : 0 ≤ κ) :
    kappaW a (LpW a + 1 * κ) = κ ∧ kappaW a (LmW a + -1 * κ) = κ := by
  unfold kappaW
  constructor
  · have e1 : LpW a + 1 * κ - LpW a = κ := by ring
    have e2 : LmW a - (LpW a + 1 * κ) ≤ κ := by linarith
    rw [e1, max_eq_left e2, max_eq_left hκ]
  · have e1 : LmW a + -1 * κ - LpW a ≤ κ := by linarith
    have e2 : LmW a - (LmW a + -1 * κ) = κ := by ring
    rw [e2, max_eq_right e1, max_eq_left hκ]

/-- `κ ≤ τ_S⁻¹ min(κ, 1)` for `0 < κ ≤ τ_S⁻¹`, `τ_S ≤ 1`. -/
private lemma aux_kappa_le {κ τS : ℝ} (hκ : 0 < κ) (hκS : κ ≤ τS⁻¹) (hτS : 0 < τS)
    (hτS1 : τS ≤ 1) : κ ≤ τS⁻¹ * min κ 1 := by
  have hτS1' : 1 ≤ τS⁻¹ := one_le_inv₀ hτS |>.2 hτS1
  rcases le_total κ 1 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h, mul_one]; exact hκS

/-- The union bound of the exclusion: `T ⊆ Gᶜ ∪ ⋃_{(j,k)} F_{jk}` over `N n` events, each of
probability `≤ N^{−D−2}`, gives `P(T) ≤ N^{−D}` once `N ≥ n + 1`. -/
private lemma aux_union {Ω : Type} [MeasureSpace Ω] {N n : ℕ} (hnN : n + 1 ≤ N) {D : ℝ}
    {T G : Set Ω} {F : Fin N × Fin n → Set Ω} (hT : T ⊆ Gᶜ ∪ ⋃ q, F q)
    (hG : ℙ Gᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))))
    (hF : ∀ q, ℙ (F q) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2)))) :
    ℙ T ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  set r := (N : ℝ) ^ (-(D + 2)) with hr
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr0 : 0 ≤ r := by positivity
  have hcard : (Fintype.card (Fin N × Fin n) : ℝ) = N * n := by simp
  calc ℙ T ≤ ℙ (Gᶜ ∪ ⋃ q, F q) := measure_mono hT
    _ ≤ ℙ Gᶜ + ℙ (⋃ q, F q) := measure_union_le _ _
    _ ≤ ENNReal.ofReal r + ∑ _q : Fin N × Fin n, ENNReal.ofReal r :=
        add_le_add hG ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun q _ => hF q))
    _ = ENNReal.ofReal (r + N * n * r) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hr0), ← ENNReal.ofReal_add hr0
          (Finset.sum_nonneg fun _ _ => hr0)]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : r = (N : ℝ) ^ (-D) * ((N : ℝ) ^ 2)⁻¹ := by
          rw [hr, show -(D + 2) = -D + -2 by ring, Real.rpow_add hN, Real.rpow_neg hN.le 2,
            Real.rpow_two]
        have hnN' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hnN
        have hND : 0 < (N : ℝ) ^ (-D) := by positivity
        have h2 : 1 + (N : ℝ) * n ≤ (N : ℝ) ^ 2 := by nlinarith
        rw [e]
        have : (N : ℝ) ^ (-D) * ((N : ℝ) ^ 2)⁻¹ + N * n * ((N : ℝ) ^ (-D) * ((N : ℝ) ^ 2)⁻¹) =
            (N : ℝ) ^ (-D) * ((1 + N * n) / (N : ℝ) ^ 2) := by ring
        rw [this]
        refine mul_le_of_le_one_right hND.le ?_
        rw [div_le_one (by positivity)]
        exact h2

/-- The exclusion of §10 ((tur1), (tur2)) adapted to `W + A` (§12.4): if `‖W‖ ≤ C₀` with high
probability and `N⁻¹ tr(W + A − z)⁻¹ − m^W = O_≺(N^{−c}(Nη)⁻¹)` on `𝐒_τ` with `τ_S ≤ ε`, the
extreme eigenvalues of `W + A` are rigid. -/
theorem rigid_of_outside (τ τS C₀ c ε D : ℝ) (hτ : 0 < τ) (hττS : τ ≤ τS / 4)
    (hτS1 : τS ≤ 1 / 4) (hτSε : τS ≤ ε) (hC₀ : 0 ≤ C₀) (hc : 0 < c) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (A : Matrix (Fin N) (Fin N) ℝ)
      (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → C₀ + 2 * ‖A‖ ≤ τS⁻¹ → (∀ ω, (W ω)ᵀ = W ω) →
      StandingBoundW τ (specOf A) (domW τ N) →
      HighProbAt N D₁ {ω | ‖W ω‖ ≤ C₀} →
      AveragedPhiLawWAt N ε₁ D₁ A W (outDomW τS (specOf A))
        (fun z => (N : ℝ) ^ (-c) / (N * z.im)) →
      RigidExtremesWAt N ε D (specOf A) (fun ω => W ω + A) := by
  have hτS : 0 < τS := by linarith
  have hτS1' : τS ≤ 1 := by linarith
  set n := ⌈2 / τS⌉₊ with hn_def
  have hn2 : 2 / τS ≤ n := Nat.le_ceil _
  have hnτ : 2 ≤ (n : ℝ) * τS := by rwa [div_le_iff₀ hτS] at hn2
  have hn1 : 1 ≤ n := by
    have : n ≠ 0 := by
      intro h0
      rw [h0] at hnτ
      norm_num at hnτ
    omega
  obtain ⟨cT, K, hcT, hK, NT, hT⟩ := im_mW_tur_le hτ n hn1
  obtain ⟨NG, hG⟩ := xpW_sub_ge hτ
  set S := ∑ k ∈ Finset.Icc 1 n, |turC n k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (aux_eventually (c := c) (K := K) (S := S) (cT := cT) hτS hc hK hS0 hcT hn1 hnτ)
  refine ⟨c / 2, D + 2, by positivity, max (max N₁ NT) (max NG (n + 1)), ?_⟩
  intro N hN Ω _ _ A W hA hAn hW hSB hnorm hlaw
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNT' : NT ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNG' : NG ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hnN : n + 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨C1, C2, C3, C4, C5⟩ := hN₁ N hN₁'
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  set a := specOf A with ha_def
  have hAn0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hτinv : 4 * τS⁻¹ ≤ τ⁻¹ := by
    have := inv_anti₀ hτ hττS
    rwa [inv_div, div_eq_mul_inv] at this
  have hτS4 : 4 ≤ τS⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hτS]
    linarith
  have haA : ∀ i, |a i| ≤ ‖A‖ := abs_specOf_le_norm hA
  have ha' : ∀ i, |a i| ≤ τ⁻¹ - 2 := fun i => (haA i).trans (by linarith)
  have ha'n : ∀ i, |(-a) i| ≤ τ⁻¹ - 2 := fun i => by rw [Pi.neg_apply, abs_neg]; exact ha' i
  obtain ⟨hLp, hLm, hLL⟩ := aux_L_facts hN1 hτ (hG N hNG' a ha' hSB) haA
  have hLneg : LpW (-a) = -LmW a := by linarith [LmW_neg a]
  have hH : ∀ ω, (W ω + A).IsHermitian := fun ω => by
    have hWh : (W ω).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [conjTranspose_eq_transpose_of_trivial]
      exact hW ω
    exact hWh.add hA
  have heig : ∀ ω i, |specOf (W ω + A) i| ≤ ‖W ω‖ + ‖A‖ := fun ω i =>
    (abs_specOf_le_norm (hH ω) i).trans (norm_add_le _ _)
  set u : ℝ := (N : ℝ) ^ (-2 / 3 + τS) with hu_def
  set h : ℝ := (N : ℝ) ^ (-2 / 3 : ℝ) with hh_def
  set p : ℝ := (N : ℝ) ^ (-τS) with hp_def
  set δ : ℝ := (N : ℝ) ^ (c / 2) * (N : ℝ) ^ (-c) / N with hδ_def
  have hu : 0 < u := by positivity
  have hh : 0 < h := by positivity
  have hp : 0 < p := by positivity
  have hpu : p * u = h := by
    rw [hp_def, hu_def, hh_def, ← Real.rpow_add hNr]
    ring_nf
  have hut : u ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    rw [hu_def, ← Real.rpow_add hNr]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
  -- the hypothesis `nη² ≤ (c_T min(κ,1))²` of the counterpart of (tur2)
  have hcond : ∀ κ : ℝ, 0 < κ → κ ≤ τS⁻¹ → (n : ℝ) * (p * κ) ^ 2 ≤ (cT * min κ 1) ^ 2 := by
    intro κ hκ hκS
    have hk := aux_kappa_le hκ hκS hτS hτS1'
    have h1 : p * κ ≤ p * τS⁻¹ * min κ 1 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hk hp.le
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    have hn0 : (0 : ℝ) ≤ n := by positivity
    calc (n : ℝ) * (p * κ) ^ 2 ≤ n * (p * τS⁻¹ * min κ 1) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hn0
      _ = (n * (p * τS⁻¹) ^ 2) * (min κ 1) ^ 2 := by ring
      _ ≤ cT ^ 2 * (min κ 1) ^ 2 := mul_le_mul_of_nonneg_right C3 (sq_nonneg _)
      _ = (cT * min κ 1) ^ 2 := by ring
  -- the nodes lie in `𝐒_τ`
  have hnode : ∀ s L : ℝ, (∀ κ : ℝ, 0 ≤ κ → kappaW a (L + s * κ) = κ) → ∀ j : ℕ,
      u + j * h ≤ τS⁻¹ → ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (⟨L + s * (u + j * h), √(k : ℝ) * (p * (u + j * h))⟩ : ℂ) ∈ outDomW τS a := by
    intro s L hkap j hκS k hk1 hkn
    have hj0 : (0 : ℝ) ≤ j * h := by positivity
    have hκ0 : 0 < u + j * h := by linarith
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hsk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 hk1'
    have hskn : √(k : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hkn'
    unfold outDomW
    simp only [Set.mem_ofPred_eq]
    rw [hkap _ hκ0.le]
    refine ⟨by linarith, hκS, ?_, ?_⟩
    · exact le_mul_of_one_le_left (mul_pos hp hκ0).le hsk
    · calc √(k : ℝ) * (p * (u + j * h)) ≤ √(n : ℝ) * (p * (u + j * h)) :=
            mul_le_mul_of_nonneg_right hskn (by positivity)
        _ = (√(n : ℝ) * p) * (u + j * h) := by ring
        _ ≤ (N : ℝ) ^ (-τS / 2) * (u + j * h) := mul_le_mul_of_nonneg_right C4 hκ0.le
  -- the bound at a node off the exceptional event
  have hgood : ∀ ω (z : ℂ) (η : ℝ) (k : ℕ), 1 ≤ k → 0 < η → z.im = √(k : ℝ) * η →
      ¬ ((N : ℝ) ^ (c / 2) * ((N : ℝ) ^ (-c) / (N * z.im)) < ‖mNW A (W ω) z - mW a z‖) →
      ‖empStieltjes (specOf (W ω + A)) z - mW a z‖ ≤ δ / η := by
    intro ω z η k hk hη hz hn
    push Not at hn
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.2 hk1'
    have hzi : η ≤ z.im := by rw [hz]; exact le_mul_of_one_le_left hη.le hsk
    have hzi0 : 0 < z.im := by linarith
    rw [← aux_mNW_eq (hH ω) hzi0]
    refine hn.trans ?_
    have h1 : (N : ℝ) ^ (-c) / (N * z.im) ≤ (N : ℝ) ^ (-c) / (N * η) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hzi hNr.le)
    calc (N : ℝ) ^ (c / 2) * ((N : ℝ) ^ (-c) / (N * z.im))
        ≤ (N : ℝ) ^ (c / 2) * ((N : ℝ) ^ (-c) / (N * η)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = δ / η := by rw [hδ_def]; field_simp
  -- the exceptional events
  have hFmeas : ∀ (zf : Fin N × Fin n → ℂ) (q : Fin N × Fin n),
      ℙ {ω | zf q ∈ outDomW τS a ∧ (N : ℝ) ^ (c / 2) * ((N : ℝ) ^ (-c) / (N * (zf q).im)) <
        ‖mNW A (W ω) (zf q) - mW a (zf q)‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    intro zf q
    by_cases hm : zf q ∈ outDomW τS a
    · refine le_trans ?_ (hlaw (zf q) hm)
      exact measure_mono fun ω hω => hω.2
    · simp [hm]
  have hκpos : ∀ j : ℕ, 0 < u + j * h := fun j => by
    have : (0 : ℝ) ≤ j * h := by positivity
    linarith
  unfold RigidExtremesWAt RigidExtremesAt DomAt
  refine ⟨?_, ?_⟩
  · -- the right edge
    set zR : Fin N × Fin n → ℂ := fun q => ⟨LpW a + 1 * (u + ((q.1 : ℕ) : ℝ) * h),
      √((((q.2 : ℕ) + 1 : ℕ)) : ℝ) * (p * (u + ((q.1 : ℕ) : ℝ) * h))⟩ with hzR
    refine aux_union (G := {ω | ‖W ω‖ ≤ C₀}) hnN ?_ hnorm (hFmeas zR)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, not_or,
      not_not, not_exists] at hcon
    obtain ⟨hWn, hF⟩ := hcon
    have key := aux_side hn1 (specOf (W ω + A)) (mW a) (L := LpW a) (s := 1) (by norm_num)
      hτS hτS1' hK hu hh hp hpu ?_ C5 C1 C2 ?_ ?_
    · have hlam : sortedEig (W ω + A) 1 < LpW a + u := by
        by_contra hge
        push Not at hge
        have h1 := (sortedEig_ge_iff (hH ω) le_rfl hN1 (LpW a + u)).1 hge
        unfold eigCount at h1
        obtain ⟨i, hi⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one h1)
        rw [Finset.mem_filter] at hi
        have := key i
        linarith [hi.2]
      have : max (sortedEig (W ω + A) 1 - LpW a) 0 ≤ u := max_le (by linarith) hu.le
      linarith
    · intro i
      have h1 := (abs_le.1 (heig ω i)).2
      linarith
    · intro j hj hκS
      have hκ := hκpos j
      have e : LpW a + 1 * (u + j * h) - LpW a = u + j * h := by ring
      have hc' : (n : ℝ) * (p * (u + j * h)) ^ 2 ≤
          (cT * min (LpW a + 1 * (u + j * h) - LpW a) 1) ^ 2 := by
        rw [e]; exact hcond _ hκ hκS
      have := hT N hNT' a ha' hSB (LpW a + 1 * (u + j * h)) (p * (u + j * h)) (by linarith)
        (by positivity) hc'
      rwa [e] at this
    · intro j hj hκS k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk'n : k' < n := by omega
      have hmem : zR (⟨j, hj⟩, ⟨k', hk'n⟩) ∈ outDomW τS a :=
        hnode 1 (LpW a) (fun κ hκ => (aux_kappa hLL hκ).1) j hκS (k' + 1) hk1 hkn
      have hlt := fun hh' => hF (⟨j, hj⟩, ⟨k', hk'n⟩) ⟨hmem, hh'⟩
      exact hgood ω (zR (⟨j, hj⟩, ⟨k', hk'n⟩)) (p * (u + j * h)) (k' + 1) hk1
        (by positivity) rfl hlt
  · -- the left edge
    set zL : Fin N × Fin n → ℂ := fun q => ⟨LmW a + -1 * (u + ((q.1 : ℕ) : ℝ) * h),
      √((((q.2 : ℕ) + 1 : ℕ)) : ℝ) * (p * (u + ((q.1 : ℕ) : ℝ) * h))⟩ with hzL
    refine aux_union (G := {ω | ‖W ω‖ ≤ C₀}) hnN ?_ hnorm (hFmeas zL)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, not_or,
      not_not, not_exists] at hcon
    obtain ⟨hWn, hF⟩ := hcon
    have key := aux_side hn1 (specOf (W ω + A)) (mW a) (L := LmW a) (s := -1) (by norm_num)
      hτS hτS1' hK hu hh hp hpu ?_ C5 C1 C2 ?_ ?_
    · have hall : eigCount (W ω + A) (LmW a - u) = N := by
        unfold eigCount
        rw [Finset.filter_true_of_mem fun i _ => by have := key i; linarith, Finset.card_univ,
          Fintype.card_fin]
      have hlam : LmW a - u ≤ sortedEig (W ω + A) N :=
        (sortedEig_ge_iff (hH ω) hN1 le_rfl (LmW a - u)).2 (by rw [hall])
      have : max (LmW a - sortedEig (W ω + A) N) 0 ≤ u := max_le (by linarith) hu.le
      linarith
    · intro i
      have h1 := (abs_le.1 (heig ω i)).1
      linarith
    · intro j hj hκS
      have hκ := hκpos j
      have e : -(LmW a + -1 * (u + j * h)) - LpW (-a) = u + j * h := by rw [hLneg]; ring
      have hc' : (n : ℝ) * (p * (u + j * h)) ^ 2 ≤
          (cT * min (-(LmW a + -1 * (u + j * h)) - LpW (-a)) 1) ^ 2 := by
        rw [e]; exact hcond _ hκ hκS
      have := hT N hNT' (-a) ha'n (aux_sb_neg hN1 hSB) (-(LmW a + -1 * (u + j * h)))
        (p * (u + j * h)) (by rw [hLneg]; linarith) (by positivity) hc'
      rw [e] at this
      refine le_trans (le_of_eq ?_) this
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
      rw [aux_im_neg hN1 a (mul_pos (Real.sqrt_pos.2 hk0) (mul_pos hp hκ))]
    · intro j hj hκS k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk'n : k' < n := by omega
      have hmem : zL (⟨j, hj⟩, ⟨k', hk'n⟩) ∈ outDomW τS a :=
        hnode (-1) (LmW a) (fun κ hκ => (aux_kappa hLL hκ).2) j hκS (k' + 1) hk1 hkn
      have hlt := fun hh' => hF (⟨j, hj⟩, ⟨k', hk'n⟩) ⟨hmem, hh'⟩
      exact hgood ω (zL (⟨j, hj⟩, ⟨k', hk'n⟩)) (p * (u + j * h)) (k' + 1) hk1
        (by positivity) rfl hlt

#print axioms Anisotropic.rigid_of_outside

end Anisotropic
