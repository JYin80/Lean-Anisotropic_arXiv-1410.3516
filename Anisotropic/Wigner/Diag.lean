module

public import Anisotropic.Comparison.Ladder
public import Anisotropic.Comparison.Props
public import Anisotropic.Comparison.Words
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.Props
public import Anisotropic.Wigner.RoughBound
public import Anisotropic.Wigner.SelfConsistentII
public import Anisotropic.Wigner.Words

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Lemma 12.7: the diagonal coefficients -/

/-! ## The spectral form of `G^W` -/

/-- A real symmetric `M` is `U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma diag_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
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
private lemma diag_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
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
private lemma diag_testNorm_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- The sandwich `⟨v, U D Uᵀ w⟩ = ∑ₖ dₖ (Uᵀ v)ₖ (Uᵀ w)ₖ`. -/
private lemma diag_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
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
private lemma diag_spectral {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) : ∃ (U : Matrix (Fin N) (Fin N) ℝ) (l : Fin N → ℝ), U * Uᵀ = 1 ∧
      Uᵀ * U = 1 ∧ ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (GW A Wm z) v w =
        ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ) := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := diag_eig_decomp (hW'.add hA)
  refine ⟨U, l, hUU, hUU', fun z hz v w => ?_⟩
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    diag_resolvent_eq hUU hUU' hMU hne
  rw [hG, diag_ent_sandwich]

/-- `Σₖ ((Uᵀ v)ₖ)² = |v|²`. -/
private lemma diag_sum_sq {N : ℕ} {U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1)
    (v : Fin N → ℝ) : ∑ k, (Uᵀ *ᵥ v) k ^ 2 = testNorm v ^ 2 := by
  rw [← diag_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v]
  unfold testNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- `G^W` is symmetric as a bilinear form. -/
private lemma diag_ent_symm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x y : Fin N → ℝ) :
    ent (GW A Wm z) x y = ent (GW A Wm z) y x := by
  obtain ⟨U, l, -, -, hs⟩ := diag_spectral hA hW
  rw [hs z hz, hs z hz]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm ((Uᵀ *ᵥ x) k)]

/-- `|G_{xy}| ≤ |x||y| / Im z`. -/
private lemma diag_ent_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x y : Fin N → ℝ) :
    ‖ent (GW A Wm z) x y‖ ≤ z.im⁻¹ * testNorm x * testNorm y := by
  obtain ⟨U, l, hUU, -, hs⟩ := diag_spectral hA hW
  rw [hs z hz]
  have hd : ∀ k, ‖((l k : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
    intro k
    rw [norm_inv]
    refine inv_anti₀ hz ?_
    have := Complex.abs_im_le_norm ((l k : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    exact (le_abs_self z.im).trans this
  calc ‖∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ x) k * (Uᵀ *ᵥ y) k : ℝ) : ℂ)‖
      ≤ ∑ k, ‖((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ x) k * (Uᵀ *ᵥ y) k : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k, z.im⁻¹ * (|(Uᵀ *ᵥ x) k| * |(Uᵀ *ᵥ y) k|) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hd k) (by positivity)
    _ = z.im⁻¹ * ∑ k, |(Uᵀ *ᵥ x) k| * |(Uᵀ *ᵥ y) k| := by rw [Finset.mul_sum]
    _ ≤ z.im⁻¹ * (testNorm x * testNorm y) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hz.le)
        refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
        simp only [sq_abs]
        rw [diag_sum_sq hUU, diag_sum_sq hUU, Real.sqrt_sq (by unfold testNorm; positivity),
          Real.sqrt_sq (by unfold testNorm; positivity)]
    _ = _ := by ring

/-- The Ward identity `∑ᵢ |G_{x eᵢ}|² = Im G_{xx} / Im z`. -/
private lemma diag_ward {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x : Fin N → ℝ) :
    ∑ i, ‖ent (GW A Wm z) x (eI i)‖ ^ 2 = (ent (GW A Wm z) x x).im / z.im := by
  obtain ⟨U, l, hUU, hUU', hs⟩ := diag_spectral hA hW
  set d : Fin N → ℂ := fun k => ((l k : ℂ) - z)⁻¹ with hd
  set u : Fin N → ℝ := fun k => (Uᵀ *ᵥ x) k with hu
  have hUe : ∀ i k, (Uᵀ *ᵥ eI i) k = U i k := by
    intro i k
    simp [eI, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hg : ∀ i, ent (GW A Wm z) x (eI i) = ∑ k, d k * ((u k * U i k : ℝ) : ℂ) := by
    intro i
    rw [hs z hz]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hUe]
  have hre : ∀ i, (ent (GW A Wm z) x (eI i)).re = (U *ᵥ fun k => (d k).re * u k) i := by
    intro i
    rw [hg, Complex.re_sum]
    simp only [Matrix.mulVec, dotProduct, Complex.re_mul_ofReal]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have him : ∀ i, (ent (GW A Wm z) x (eI i)).im = (U *ᵥ fun k => (d k).im * u k) i := by
    intro i
    rw [hg, Complex.im_sum]
    simp only [Matrix.mulVec, dotProduct, Complex.im_mul_ofReal]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnorm : ∀ c : Fin N → ℝ, ∑ i, (U *ᵥ c) i ^ 2 = ∑ k, c k ^ 2 := by
    intro c
    have h := diag_testNorm_orth (Q := U) hUU' c
    have h2 : testNorm (U *ᵥ c) ^ 2 = testNorm c ^ 2 := by rw [h]
    unfold testNorm at h2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
  have hl : ∀ i, ‖ent (GW A Wm z) x (eI i)‖ ^ 2 =
      (U *ᵥ fun k => (d k).re * u k) i ^ 2 + (U *ᵥ fun k => (d k).im * u k) i ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  simp only [hl]
  rw [Finset.sum_add_distrib, hnorm, hnorm, hs z hz x x, Complex.im_sum, Finset.sum_div,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdk : (d k).im = z.im / Complex.normSq ((l k : ℂ) - z) := by
    simp only [hd]
    rw [Complex.inv_im]
    simp
  have hdn : (d k).re ^ 2 + (d k).im ^ 2 = (Complex.normSq ((l k : ℂ) - z))⁻¹ := by
    have h1 := Complex.normSq_apply (d k)
    have h2 : Complex.normSq (d k) = (Complex.normSq ((l k : ℂ) - z))⁻¹ := by
      simp only [hd, map_inv₀]
    rw [h2] at h1
    rw [h1]; ring
  rw [Complex.im_mul_ofReal]
  have hq : Complex.normSq ((l k : ℂ) - z) ≠ 0 := by
    intro h
    have := (Complex.normSq_eq_zero).1 h
    have h3 := congrArg Complex.im this
    simp at h3
    linarith
  change ((d k).re * u k) ^ 2 + ((d k).im * u k) ^ 2 = (d k).im * (u k * u k) / z.im
  have : ((d k).re * u k) ^ 2 + ((d k).im * u k) ^ 2 = ((d k).re ^ 2 + (d k).im ^ 2) * u k ^ 2 := by
    ring
  rw [this, hdn]
  rw [hdk]
  field_simp

/-! ## The coefficient `f₂` of `F_v^p` -/

/-- A tuple of naturals with sum `2` is `2` at one place, or `1` at two distinct places. -/
private lemma diag_tuple_cases {p : ℕ} (k : Fin p → ℕ) (hk : ∑ r, k r = 2) :
    (∃ r : Fin p, k = fun s => if s = r then 2 else 0) ∨
    (∃ r s : Fin p, r ≠ s ∧ k = fun u => if u = r ∨ u = s then 1 else 0) := by
  by_cases h2 : ∃ r, 2 ≤ k r
  · left
    obtain ⟨r, hr⟩ := h2
    refine ⟨r, ?_⟩
    have hsum := Finset.add_sum_erase Finset.univ k (Finset.mem_univ r)
    have hkr : k r = 2 := by
      have : 0 ≤ ∑ s ∈ Finset.univ.erase r, k s := Nat.zero_le _
      omega
    have hz : ∑ s ∈ Finset.univ.erase r, k s = 0 := by omega
    funext s
    by_cases hs : s = r
    · subst hs; simp [hkr]
    · have := (Finset.sum_eq_zero_iff.1 hz) s (Finset.mem_erase.2 ⟨hs, Finset.mem_univ s⟩)
      simp [hs, this]
  · right
    push Not at h2
    have h1 : ∀ r, k r = 0 ∨ k r = 1 := fun r => by have := h2 r; omega
    have hcard : (Finset.univ.filter fun r => k r = 1).card = 2 := by
      rw [← hk, Finset.card_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      rcases h1 r with h | h <;> simp [h]
    obtain ⟨r, s, hrs, hU⟩ := Finset.card_eq_two.1 hcard
    refine ⟨r, s, hrs, ?_⟩
    funext u
    have hu : k u = 1 ↔ u = r ∨ u = s := by
      have := Finset.ext_iff.1 hU u
      simpa using this
    by_cases huu : u = r ∨ u = s
    · simp [huu, hu.2 huu]
    · have : k u ≠ 1 := fun h => huu (hu.1 h)
      have h0 : k u = 0 := (h1 u).resolve_right this
      simp [huu, h0]

/-- The product over a tuple that is `2` at `r` and `0` elsewhere. -/
private lemma diag_prod_single {p : ℕ} (b : ℕ → ℝ) (r : Fin p) :
    ∏ u : Fin p, b (if u = r then 2 else 0) = b 2 * b 0 ^ (p - 1) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
  have : ∏ u ∈ Finset.univ.erase r, b (if u = r then 2 else 0) = b 0 ^ (p - 1) := by
    rw [Finset.prod_congr rfl (g := fun _ => b 0)]
    · simp [Finset.card_erase_of_mem]
    · intro u hu
      simp [(Finset.mem_erase.1 hu).1]
  rw [this]; simp

/-- The product over a tuple that is `1` at two distinct places and `0` elsewhere. -/
private lemma diag_prod_pair {p : ℕ} (b : ℕ → ℝ) (r s : Fin p) (hrs : r ≠ s) :
    ∏ u : Fin p, b (if u = r ∨ u = s then 1 else 0) = b 1 * b 1 * b 0 ^ (p - 2) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
  have hs : s ∈ Finset.univ.erase r := Finset.mem_erase.2 ⟨hrs.symm, Finset.mem_univ s⟩
  rw [← Finset.mul_prod_erase _ _ hs]
  have : ∏ u ∈ (Finset.univ.erase r).erase s, b (if u = r ∨ u = s then 1 else 0) =
      b 0 ^ (p - 2) := by
    rw [Finset.prod_congr rfl (g := fun _ => b 0)]
    · rw [Finset.prod_const, Finset.card_erase_of_mem hs,
        Finset.card_erase_of_mem (Finset.mem_univ r)]
      simp; congr 1
    · intro u hu
      have h1 := (Finset.mem_erase.1 hu)
      have h2 := Finset.mem_erase.1 h1.2
      simp [h1.1, h2.1]
  rw [this]; simp [hrs.symm]; ring

/-- `‖f₂‖ ≤ p |a₂| |a₀|^{p−1} + p² |a₁|² |a₀|^{p−2}`. -/
private lemma diag_fCoeff_le {p : ℕ} (a : ℕ → ℂ) :
    ‖fCoeff p a 2‖ ≤ p * (‖a 2‖ * ‖a 0‖ ^ (p - 1)) + p ^ 2 * (‖a 1‖ ^ 2 * ‖a 0‖ ^ (p - 2)) := by
  set b : ℕ → ℝ := fun k => ‖a k‖ with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => norm_nonneg _
  have h1 : ‖fCoeff p a 2‖ ≤ ∑ k ∈ Finset.Nat.antidiagonalTuple p 2, ∏ r : Fin p, b (k r) := by
    unfold fCoeff
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_prod]
    refine le_of_eq (Finset.prod_congr rfl fun r _ => ?_)
    split_ifs <;> simp [hb]
  refine h1.trans ?_
  set g1 : Fin p → Fin p → ℕ := fun r s => if s = r then 2 else 0 with hg1
  set g2 : Fin p × Fin p → Fin p → ℕ := fun rs u => if u = rs.1 ∨ u = rs.2 then 1 else 0 with hg2
  set h : (Fin p → ℕ) → ℝ := fun k => ∏ r : Fin p, b (k r) with hh
  have hh0 : ∀ k, 0 ≤ h k := fun k => Finset.prod_nonneg fun r _ => hb0 _
  have hsub : Finset.Nat.antidiagonalTuple p 2 ⊆
      Finset.univ.image g1 ∪ (Finset.univ.offDiag).image g2 := by
    intro k hk
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    rcases diag_tuple_cases k hk with ⟨r, hr⟩ | ⟨r, s, hrs, hrs'⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, Finset.mem_univ _, hr.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(r, s), Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hrs⟩, hrs'.symm⟩)
  calc ∑ k ∈ Finset.Nat.antidiagonalTuple p 2, h k
      ≤ ∑ k ∈ Finset.univ.image g1 ∪ (Finset.univ.offDiag).image g2, h k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hh0 k
    _ ≤ ∑ k ∈ Finset.univ.image g1, h k + ∑ k ∈ (Finset.univ.offDiag).image g2, h k := by
        have := Finset.sum_union_inter (s₁ := Finset.univ.image g1)
          (s₂ := (Finset.univ.offDiag).image g2) (f := h)
        have h0 : 0 ≤ ∑ k ∈ Finset.univ.image g1 ∩ (Finset.univ.offDiag).image g2, h k :=
          Finset.sum_nonneg fun k _ => hh0 k
        linarith
    _ ≤ ∑ r : Fin p, h (g1 r) + ∑ rs ∈ (Finset.univ : Finset (Fin p)).offDiag, h (g2 rs) :=
        add_le_add (Finset.sum_image_le_of_nonneg fun k _ => hh0 k)
          (Finset.sum_image_le_of_nonneg fun k _ => hh0 k)
    _ ≤ p * (b 2 * b 0 ^ (p - 1)) + p ^ 2 * (b 1 ^ 2 * b 0 ^ (p - 2)) := by
        have e1 : ∀ r : Fin p, h (g1 r) = b 2 * b 0 ^ (p - 1) := fun r => diag_prod_single b r
        have e2 : ∀ rs ∈ (Finset.univ : Finset (Fin p)).offDiag,
            h (g2 rs) = b 1 ^ 2 * b 0 ^ (p - 2) := by
          intro rs hrs
          have := diag_prod_pair b rs.1 rs.2 (Finset.mem_offDiag.1 hrs).2.2
          simp only [hh, hg2]
          rw [this]; ring
        rw [Finset.sum_congr rfl fun r _ => e1 r, Finset.sum_congr rfl e2]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        refine add_le_add (le_of_eq rfl) ?_
        rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul_of_nonneg_right ?_ (by have := hb0 1; have := hb0 0; positivity)
        have : p * p - p ≤ p * p := Nat.sub_le _ _
        rw [sq]; exact_mod_cast this

/-- `‖f₂‖` for `p = q + 2`, in terms of `a₀, a₁, a₂`. -/
private lemma diag_fCoeff_le' (q : ℕ) (a : ℕ → ℂ) :
    ‖fCoeff (q + 2) a 2‖ ≤ ((q : ℝ) + 2) * (‖a 2‖ * ‖a 0‖ ^ (q + 1)) +
      ((q : ℝ) + 2) ^ 2 * (‖a 1‖ ^ 2 * ‖a 0‖ ^ q) := by
  have h := diag_fCoeff_le (p := q + 2) a
  have e1 : q + 2 - 1 = q + 1 := by omega
  have e2 : q + 2 - 2 = q := by omega
  rw [e1, e2] at h
  push_cast at h
  exact h

/-! ## The coefficients `a₀, a₁, a₂` along a diagonal entry -/

/-- `X E_{ii}` keeps the `i`-th column of `X`. -/
private lemma diag_mul_delta_left {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i s b : Fin N) :
    (X * deltaW i i) s b = if b = i then X s i else 0 := by
  simp only [Matrix.mul_apply, deltaW]
  by_cases hb : b = i
  · subst hb
    simp
  · simp [hb]

/-- `X E_{ii} Y` is the rank-one matrix `(s, t) ↦ X_{si} Y_{it}`. -/
private lemma diag_mul_delta {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    X * deltaW i i * Y = fun s t => X s i * Y i t := by
  ext s t
  rw [Matrix.mul_apply]
  simp [diag_mul_delta_left]

/-- `⟨x, X e_i⟩ = ∑ₛ xₛ X_{si}`. -/
private lemma diag_ent_eI_right {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (x : Fin N → ℝ) : ent X x (eI i) = ∑ s, (x s : ℂ) * X s i := by
  simp [ent, cvec, dotProduct, mulVec, eI, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ))]

/-- `⟨e_i, Y y⟩ = ∑ₜ Y_{it} yₜ`. -/
private lemma diag_ent_eI_left {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (y : Fin N → ℝ) : ent Y (eI i) y = ∑ t, Y i t * (y t : ℂ) := by
  simp [ent, cvec, dotProduct, mulVec, eI, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ))]

/-- `⟨x, X E_{ii} Y y⟩ = ⟨x, X e_i⟩ ⟨e_i, Y y⟩`. -/
private lemma diag_ent_delta {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (x y : Fin N → ℝ) :
    ent (X * deltaW i i * Y) x y = ent X x (eI i) * ent Y (eI i) y := by
  rw [diag_mul_delta, diag_ent_eI_right, diag_ent_eI_left, Finset.sum_mul_sum]
  simp only [ent, cvec, dotProduct, mulVec]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `a₀ = (G − Π)_{vv}`. -/
private lemma diag_res_zero {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i : Fin N) : resCoeffW A Wm z v i i 0 = ent (GW A Wm z - piW A z) v v := by
  simp [resCoeffW]

/-- `|a₁| = |G_{v e_i}|²`. -/
private lemma diag_res_one {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i : Fin N) :
    ‖resCoeffW A Wm z v i i 1‖ = ‖ent (GW A Wm z) v (eI i)‖ ^ 2 := by
  have h : resCoeffW A Wm z v i i 1 = -(ent (GW A Wm z) v (eI i) * ent (GW A Wm z) (eI i) v) := by
    simp only [resCoeffW, pow_one, one_ne_zero, ite_false, sub_zero, neg_mul, one_mul]
    rw [← Matrix.mul_assoc, diag_ent_delta]
  rw [h, norm_neg, norm_mul, diag_ent_symm hA hW hz (eI i) v, sq]

/-- `|a₂| = |G_{v e_i}|² |G_{ii}|`. -/
private lemma diag_res_two {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i : Fin N) :
    ‖resCoeffW A Wm z v i i 2‖ = ‖ent (GW A Wm z) v (eI i)‖ ^ 2 * ‖GW A Wm z i i‖ := by
  have h : resCoeffW A Wm z v i i 2 = ent (GW A Wm z) v (eI i) * GW A Wm z i i *
      ent (GW A Wm z) (eI i) v := by
    simp only [resCoeffW, pow_two, OfNat.ofNat_ne_zero, ite_false, sub_zero]
    have e : GW A Wm z * (deltaW i i * GW A Wm z * (deltaW i i * GW A Wm z)) =
        GW A Wm z * deltaW i i * GW A Wm z * deltaW i i * GW A Wm z := by
      simp only [Matrix.mul_assoc]
    rw [e, diag_ent_delta, diag_ent_delta, ent_eI_eI]
    ring
  rw [h, norm_mul, norm_mul, diag_ent_symm hA hW hz (eI i) v]
  ring

/-! ## Measurability -/

/-- Every entry of `G^W` is a measurable function of the matrix `W`. -/
private lemma diag_measurable_G {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s t : Fin N) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t := by
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
  rw [h]
  exact hdet.inv.mul hadj

/-- `ω ↦ ⟨x, M(ω) y⟩` is measurable when the entries of `M` are. -/
private lemma diag_measurable_ent {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {M : Ω → Matrix (Fin N) (Fin N) ℂ} (h : ∀ s t, Measurable fun ω => M ω s t)
    (x y : Fin N → ℝ) : Measurable fun ω => ent (M ω) x y := by
  have e : (fun ω => ent (M ω) x y) = fun ω => ∑ s, (x s : ℂ) * ∑ t, M ω s t * (y t : ℂ) := by
    funext ω
    simp only [ent, cvec, dotProduct, mulVec]
  rw [e]
  exact Finset.measurable_sum _ fun s _ => (Finset.measurable_sum _ fun t _ =>
    (h s t).mul_const _).const_mul _

/-- Measurability of `ω ↦ ⟨x, G^W(W ω) y⟩` and of `F_v`. -/
private lemma diag_measurable_entG {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (x y : Fin N → ℝ) :
    Measurable fun ω => ent (GW A (W ω) z) x y := by
  have hWm : Measurable W := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hW i j
  exact diag_measurable_ent (fun s t => (diag_measurable_G A z s t).comp hWm) x y

/-- `ω ↦ F_v(W ω, z)` is measurable. -/
private lemma diag_measurable_Fv {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ) :
    Measurable fun ω => FvW A (W ω) z v := by
  have hWm : Measurable W := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hW i j
  unfold FvW
  refine Measurable.norm (diag_measurable_ent (fun s t => ?_) v v)
  simp only [Matrix.sub_apply]
  exact ((diag_measurable_G A z s t).comp hWm).sub_const _

/-- `ω ↦ ⟨x, (G^W − Π^W)(W ω) y⟩` is measurable. -/
private lemma diag_measurable_entGP {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (x y : Fin N → ℝ) :
    Measurable fun ω => ent (GW A (W ω) z - piW A z) x y := by
  have hWm : Measurable W := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hW i j
  refine diag_measurable_ent (fun s t => ?_) x y
  simp only [Matrix.sub_apply]
  exact ((diag_measurable_G A z s t).comp hWm).sub_const _

/-- `⟨x, (X − Y) y⟩ = ⟨x, X y⟩ − ⟨x, Y y⟩`. -/
private lemma diag_ent_sub {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X - Y) x y = ent X x y - ent Y x y := by
  simp [ent, Matrix.sub_mulVec, dotProduct_sub]

/-- `|e_i| = 1`. -/
private lemma diag_testNorm_eI {N : ℕ} (i : Fin N) : testNorm (eI i) = 1 := by
  simp [testNorm, eI, Pi.single_apply]

/-! ## Averaging and exponent bookkeeping -/

/-- The averaging step: a pointwise bound off a measurable bad set `Bad` and a deterministic bound
on `Bad` give `N⁻¹ ∑ᵢ E fᵢ ≤ E Ψ + Bmax · P(Bad)`. -/
private lemma diag_average {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N q : ℕ} (hN : 1 ≤ N) (f s : Fin N → Ω → ℝ) (F Ψ : Ω → ℝ) (Bad : Set Ω)
    (hBad : MeasurableSet Bad) (hs : ∀ i, Measurable (s i)) (hF : Measurable F)
    (c₁ c₂ Bmax R₀ Smax Fmax β : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hB : 0 ≤ Bmax)
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hs0 : ∀ i ω, 0 ≤ s i ω) (hF0 : ∀ ω, 0 ≤ F ω)
    (hsm : ∀ i ω, s i ω ≤ Smax) (hFm : ∀ ω, F ω ≤ Fmax)
    (hfbad : ∀ i ω, f i ω ≤ Bmax)
    (hfgood : ∀ i, ∀ ω ∉ Bad, f i ω ≤ s i ω * (c₁ * F ω ^ (q + 1) + c₂ * F ω ^ q))
    (hward : ∀ ω ∉ Bad, (N : ℝ)⁻¹ * ∑ i, s i ω ≤ R₀)
    (hΨ : Integrable Ψ) (hΨ0 : ∀ ω, 0 ≤ Ψ ω)
    (hΦ : ∀ ω, R₀ * (c₁ * F ω ^ (q + 1) + c₂ * F ω ^ q) ≤ Ψ ω)
    (hβ : (ℙ : Measure Ω).real Bad ≤ β) :
    (N : ℝ)⁻¹ * ∑ i, ∫ ω, f i ω ≤ (∫ ω, Ψ ω) + Bmax * β := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set H : Ω → ℝ := fun ω => c₁ * F ω ^ (q + 1) + c₂ * F ω ^ q with hH
  have hH0 : ∀ ω, 0 ≤ H ω := fun ω => by
    have := hF0 ω
    simp only [hH]; positivity
  have hHm : Measurable H := by
    simp only [hH]
    exact ((hF.pow_const _).const_mul _).add ((hF.pow_const _).const_mul _)
  set T : Fin N → Ω → ℝ := fun i ω =>
    Bad.indicator (fun _ => Bmax) ω + Badᶜ.indicator (fun ω => s i ω * H ω) ω with hT
  have hT0 : ∀ i ω, 0 ≤ T i ω := fun i ω => by
    simp only [hT]
    refine add_nonneg (Set.indicator_nonneg (fun _ _ => hB) _) (Set.indicator_nonneg
      (fun ω _ => mul_nonneg (hs0 i ω) (hH0 ω)) _)
  have hfT : ∀ i ω, f i ω ≤ T i ω := by
    intro i ω
    by_cases hω : ω ∈ Bad
    · simp only [hT, Set.indicator_of_mem hω,
        Set.indicator_of_notMem (by simpa using hω : ω ∉ Badᶜ)]
      linarith [hfbad i ω]
    · simp only [hT, Set.indicator_of_notMem hω, Set.indicator_of_mem (show ω ∈ Badᶜ from hω)]
      linarith [hfgood i ω hω]
  have hsH : ∀ i, Integrable (fun ω => s i ω * H ω) := by
    intro i
    refine Integrable.of_bound ((hs i).mul hHm).aestronglyMeasurable
      (Smax * (c₁ * Fmax ^ (q + 1) + c₂ * Fmax ^ q)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hs0 i ω) (hH0 ω))]
    have h1 := hF0 ω
    have h2 := hFm ω
    have h3 : H ω ≤ c₁ * Fmax ^ (q + 1) + c₂ * Fmax ^ q := by
      simp only [hH]
      gcongr
    exact mul_le_mul (hsm i ω) h3 (hH0 ω) ((hs0 i ω).trans (hsm i ω))
  have hTi : ∀ i, Integrable (T i) := fun i =>
    ((integrable_const Bmax).indicator hBad).add ((hsH i).indicator hBad.compl)
  have hint : ∀ i, ∫ ω, f i ω ≤ ∫ ω, T i ω := fun i =>
    integral_mono_of_nonneg (ae_of_all _ (hf0 i)) (hTi i) (ae_of_all _ (hfT i))
  have hsum : ∑ i, ∫ ω, T i ω = ∫ ω, ∑ i, T i ω := (integral_finsetSum _ fun i _ => hTi i).symm
  set U : Ω → ℝ := fun ω => Ψ ω + Bad.indicator (fun _ => Bmax) ω with hU
  have hUi : Integrable U := hΨ.add ((integrable_const Bmax).indicator hBad)
  have hpt : ∀ ω, (N : ℝ)⁻¹ * ∑ i, T i ω ≤ U ω := by
    intro ω
    by_cases hω : ω ∈ Bad
    · simp only [hT, hU, Set.indicator_of_mem hω,
        Set.indicator_of_notMem (by simpa using hω : ω ∉ Badᶜ), add_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
      linarith [hΨ0 ω]
    · simp only [hT, hU, Set.indicator_of_notMem hω, Set.indicator_of_mem (show ω ∈ Badᶜ from hω),
        zero_add, add_zero]
      rw [← Finset.sum_mul]
      calc (N : ℝ)⁻¹ * ((∑ i, s i ω) * H ω) = ((N : ℝ)⁻¹ * ∑ i, s i ω) * H ω := by
            ring
        _ ≤ R₀ * H ω := mul_le_mul_of_nonneg_right (hward ω hω) (hH0 ω)
        _ ≤ Ψ ω := hΦ ω
  calc (N : ℝ)⁻¹ * ∑ i, ∫ ω, f i ω ≤ (N : ℝ)⁻¹ * ∑ i, ∫ ω, T i ω :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hint i) (inv_nonneg.2 hNpos.le)
    _ = ∫ ω, (N : ℝ)⁻¹ * ∑ i, T i ω := by
        rw [hsum, integral_const_mul]
    _ ≤ ∫ ω, U ω := by
        refine integral_mono (Integrable.const_mul (integrable_finsetSum _ fun i _ => hTi i) _)
          hUi hpt
    _ = (∫ ω, Ψ ω) + Bmax * (ℙ : Measure Ω).real Bad := by
        simp only [hU]
        rw [integral_add hΨ ((integrable_const Bmax).indicator hBad),
          integral_indicator_const _ hBad]
        simp [mul_comm]
    _ ≤ (∫ ω, Ψ ω) + Bmax * β := by
        have := mul_le_mul_of_nonneg_left hβ hB
        linarith

/-- `x^a w^b ≤ x^{a+b} + w^{a+b}` for nonnegative `x, w`. -/
private lemma diag_young (a b : ℕ) {x w : ℝ} (hx : 0 ≤ x) (hw : 0 ≤ w) :
    x ^ a * w ^ b ≤ x ^ (a + b) + w ^ (a + b) := by
  rcases le_total x w with h | h
  · calc x ^ a * w ^ b ≤ w ^ a * w ^ b :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx h a) (by positivity)
      _ = w ^ (a + b) := (pow_add w a b).symm
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · calc x ^ a * w ^ b ≤ x ^ a * x ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw h b) (by positivity)
      _ = x ^ (a + b) := (pow_add x a b).symm
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

/-- The exponent bookkeeping of the diagonal coefficient: with `b = n^{2(δ/4)} n^{2δ}`,
`R₀ = n^{2(δ/4)} n^{(C₀+1)δ} Ψ²` and `y = n^{C₀δ} Ψ ≤ 2`: `b R₀ ≤ y²` and `b² R₀ ≤ y²`. -/
private lemma diag_scalar {n C₀ δ Ψ : ℝ} (hn : 1 ≤ n) (hC₀ : 30 ≤ C₀) (hδ : 0 < δ) :
    n ^ (2 * (δ / 4)) * (n ^ (2 * δ) * 1 * 1) *
        (n ^ (2 * (δ / 4)) * (n ^ ((C₀ + 1) * δ) * Ψ ^ 2)) ≤ (n ^ (C₀ * δ) * Ψ) ^ 2 ∧
      (n ^ (2 * (δ / 4)) * (n ^ (2 * δ) * 1 * 1)) ^ 2 *
        (n ^ (2 * (δ / 4)) * (n ^ ((C₀ + 1) * δ) * Ψ ^ 2)) ≤ (n ^ (C₀ * δ) * Ψ) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hΨ : 0 ≤ Ψ ^ 2 := sq_nonneg _
  have hy : (n ^ (C₀ * δ) * Ψ) ^ 2 = n ^ (C₀ * δ + C₀ * δ) * Ψ ^ 2 := by
    rw [mul_pow, Real.rpow_add hn0]
    ring
  have hCδ : 30 * δ ≤ C₀ * δ := mul_le_mul_of_nonneg_right hC₀ hδ.le
  constructor
  · have e : n ^ (2 * (δ / 4)) * (n ^ (2 * δ) * 1 * 1) *
        (n ^ (2 * (δ / 4)) * (n ^ ((C₀ + 1) * δ) * Ψ ^ 2)) =
        n ^ (2 * (δ / 4) + 2 * δ + 2 * (δ / 4) + (C₀ + 1) * δ) * Ψ ^ 2 := by
      simp only [Real.rpow_add hn0]
      ring
    rw [e, hy]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)) hΨ
  · have e : (n ^ (2 * (δ / 4)) * (n ^ (2 * δ) * 1 * 1)) ^ 2 *
        (n ^ (2 * (δ / 4)) * (n ^ ((C₀ + 1) * δ) * Ψ ^ 2)) =
        n ^ (2 * (δ / 4) + 2 * δ + (2 * (δ / 4) + 2 * δ) + 2 * (δ / 4) + (C₀ + 1) * δ) * Ψ ^ 2 := by
      simp only [Real.rpow_add hn0]
      ring
    rw [e, hy]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)) hΨ

/-- The bad-event contribution: `Bmax ≤ (p + p²)(2n)^{q+4}`, `y ≥ τ/n` give
`Bmax · 3 n^{-(D_A − 2)} ≤ 3 (p + p²) 2^{q+4} τ^{-p} y^p`, `p = q + 2`, `D_A = dPrev p`. -/
private lemma diag_bad_bound {n τ y Bmax : ℝ} {q : ℕ} (hn : 1 ≤ n) (hτ : 0 < τ)
    (hy : τ / n ≤ y) (hB : Bmax ≤ (((q : ℝ) + 2) + ((q : ℝ) + 2) ^ 2) * (2 * n) ^ (q + 4)) :
    Bmax * (3 * n ^ (-(dPrev (q + 2) - 2))) ≤
      (3 * (((q : ℝ) + 2) + ((q : ℝ) + 2) ^ 2) * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2)) * y ^ (q + 2) := by
  have hn0 : 0 < n := by linarith
  set P : ℝ := ((q : ℝ) + 2) + ((q : ℝ) + 2) ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hD : dPrev (q + 2) = 100 * (((q + 2 : ℕ) : ℝ) + 1) ^ 2 := rfl
  have hexp : (q : ℝ) + 4 + (-(dPrev (q + 2) - 2)) ≤ -((q : ℝ) + 2) := by
    rw [hD]; push_cast
    nlinarith [sq_nonneg ((q : ℝ) + 3), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have h1 : n ^ (q + 4) * n ^ (-(dPrev (q + 2) - 2)) ≤ (n ^ (q + 2))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hn0, ← Real.rpow_neg hn0.le]
    refine Real.rpow_le_rpow_of_exponent_le hn ?_
    push_cast
    linarith
  have hyp : (τ / n) ^ (q + 2) ≤ y ^ (q + 2) :=
    pow_le_pow_left₀ (by positivity) hy _
  have hnq : 0 < n ^ (q + 2) := by positivity
  have hτq : 0 < τ ^ (q + 2) := by positivity
  calc Bmax * (3 * n ^ (-(dPrev (q + 2) - 2)))
      ≤ (P * (2 * n) ^ (q + 4)) * (3 * n ^ (-(dPrev (q + 2) - 2))) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
    _ = (3 * P * 2 ^ (q + 4)) * (n ^ (q + 4) * n ^ (-(dPrev (q + 2) - 2))) := by
        rw [mul_pow]; ring
    _ ≤ (3 * P * 2 ^ (q + 4)) * (n ^ (q + 2))⁻¹ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (3 * P * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2)) * (τ / n) ^ (q + 2) := by
        rw [div_pow, inv_pow]
        field_simp
    _ ≤ (3 * P * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2)) * y ^ (q + 2) :=
        mul_le_mul_of_nonneg_left hyp (by positivity)

/-! ## The size of `Ψ^W` -/

/-- `Ψ^W ≥ 0`, `Im m^W / (Nη) ≤ (Ψ^W)²` and `(Nη)⁻¹ ≤ Ψ^W`. -/
private lemma diag_psi_facts {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
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
private lemma diag_psi_small {τ : ℝ} {N : ℕ} (hN : 1 ≤ N) {C₀ δ : ℝ}
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



/-! ## The pointwise bound on `f₂` -/

/-- `|f₂|` for a symmetric `W + A`, in terms of `|G_{v e_i}|`, `|G_{ii}|` and `F_v`. -/
private lemma diag_pt {N : ℕ} (q : ℕ) {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i : Fin N) :
    ‖fCoeff (q + 2) (resCoeffW A Wm z v i i) 2‖ ≤
      ((q : ℝ) + 2) * (‖ent (GW A Wm z) v (eI i)‖ ^ 2 * ‖GW A Wm z i i‖ *
        FvW A Wm z v ^ (q + 1)) +
      ((q : ℝ) + 2) ^ 2 * ((‖ent (GW A Wm z) v (eI i)‖ ^ 2) ^ 2 * FvW A Wm z v ^ q) := by
  have h := diag_fCoeff_le' q (resCoeffW A Wm z v i i)
  have h0 : ‖resCoeffW A Wm z v i i 0‖ = FvW A Wm z v := by
    rw [diag_res_zero]; rfl
  rw [h0, diag_res_one hA hW hz, diag_res_two hA hW hz] at h
  exact h

/-- The bound of `diag_pt` when `|G_{v e_i}|` and `|G_{ii}|` are at most `B` and `F ≥ 0`. -/
private lemma diag_pt_good (q : ℕ) {g Gd F B : ℝ} (hg : g ≤ B) (hg0 : 0 ≤ g) (hGd : Gd ≤ B)
    (hF : 0 ≤ F) :
    ((q : ℝ) + 2) * (g ^ 2 * Gd * F ^ (q + 1)) + ((q : ℝ) + 2) ^ 2 * ((g ^ 2) ^ 2 * F ^ q) ≤
      g ^ 2 * (((q : ℝ) + 2) * B * F ^ (q + 1) + ((q : ℝ) + 2) ^ 2 * B ^ 2 * F ^ q) := by
  have hs : g ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hg0 hg 2
  have hs0 : 0 ≤ g ^ 2 := by positivity
  have t1 : g ^ 2 * Gd * F ^ (q + 1) ≤ g ^ 2 * B * F ^ (q + 1) := by gcongr
  have t2 : (g ^ 2) ^ 2 ≤ g ^ 2 * B ^ 2 := by
    rw [sq (g ^ 2)]
    exact mul_le_mul_of_nonneg_left hs hs0
  calc _ ≤ ((q : ℝ) + 2) * (g ^ 2 * B * F ^ (q + 1)) +
        ((q : ℝ) + 2) ^ 2 * (g ^ 2 * B ^ 2 * F ^ q) := by gcongr
    _ = _ := by ring

/-- The deterministic bound of `diag_pt`: `|G_{v e_i}|, |G_{ii}| ≤ s`, `0 ≤ F ≤ Fm`. -/
private lemma diag_pt_bad (q : ℕ) {g Gd F s Fm : ℝ} (hg : g ≤ s) (hg0 : 0 ≤ g) (hGd : Gd ≤ s)
    (hGd0 : 0 ≤ Gd) (hF : 0 ≤ F) (hFm : F ≤ Fm) :
    ((q : ℝ) + 2) * (g ^ 2 * Gd * F ^ (q + 1)) + ((q : ℝ) + 2) ^ 2 * ((g ^ 2) ^ 2 * F ^ q) ≤
      ((q : ℝ) + 2) * s ^ 3 * Fm ^ (q + 1) + ((q : ℝ) + 2) ^ 2 * s ^ 4 * Fm ^ q := by
  have hs : g ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hg0 hg 2
  have hs0 : 0 ≤ s := hg0.trans hg
  have t1 : g ^ 2 * Gd * F ^ (q + 1) ≤ s ^ 2 * s * Fm ^ (q + 1) := by gcongr
  have t2 : (g ^ 2) ^ 2 * F ^ q ≤ (s ^ 2) ^ 2 * Fm ^ q := by gcongr
  calc _ ≤ ((q : ℝ) + 2) * (s ^ 2 * s * Fm ^ (q + 1)) +
        ((q : ℝ) + 2) ^ 2 * ((s ^ 2) ^ 2 * Fm ^ q) := by gcongr
    _ = _ := by ring

/-- The Young step: `B R₀ ≤ 4y` and `B² R₀ ≤ 4y²` give
`R₀ ((q+2) B F^{q+1} + (q+2)² B² F^q) ≤ (4(q+2) + 4(q+2)²)(y^{q+2} + F^{q+2})`. -/
private lemma diag_phi (q : ℕ) {y F B R₀ : ℝ} (hy0 : 0 ≤ y) (hF : 0 ≤ F)
    (h1 : B * R₀ ≤ 4 * y) (h2 : B ^ 2 * R₀ ≤ 4 * y ^ 2) :
    R₀ * (((q : ℝ) + 2) * B * F ^ (q + 1) + ((q : ℝ) + 2) ^ 2 * B ^ 2 * F ^ q) ≤
      (4 * ((q : ℝ) + 2) + 4 * ((q : ℝ) + 2) ^ 2) * (y ^ (q + 2) + F ^ (q + 2)) := by
  have y1 := diag_young 1 (q + 1) hy0 hF
  rw [pow_one, show 1 + (q + 1) = q + 2 by omega] at y1
  have y2 := diag_young 2 q hy0 hF
  rw [show 2 + q = q + 2 by omega] at y2
  have hq2 : (0 : ℝ) ≤ (q : ℝ) + 2 := by positivity
  have c1 : R₀ * (((q : ℝ) + 2) * B * F ^ (q + 1)) ≤ ((q : ℝ) + 2) * (4 * y) * F ^ (q + 1) := by
    calc _ = ((q : ℝ) + 2) * (B * R₀) * F ^ (q + 1) := by ring
      _ ≤ _ := by gcongr
  have c2 : R₀ * (((q : ℝ) + 2) ^ 2 * B ^ 2 * F ^ q) ≤
      ((q : ℝ) + 2) ^ 2 * (4 * y ^ 2) * F ^ q := by
    calc _ = ((q : ℝ) + 2) ^ 2 * (B ^ 2 * R₀) * F ^ q := by ring
      _ ≤ _ := by gcongr
  calc R₀ * (((q : ℝ) + 2) * B * F ^ (q + 1) + ((q : ℝ) + 2) ^ 2 * B ^ 2 * F ^ q)
      = R₀ * (((q : ℝ) + 2) * B * F ^ (q + 1)) +
        R₀ * (((q : ℝ) + 2) ^ 2 * B ^ 2 * F ^ q) := by ring
    _ ≤ ((q : ℝ) + 2) * (4 * y) * F ^ (q + 1) + ((q : ℝ) + 2) ^ 2 * (4 * y ^ 2) * F ^ q :=
        add_le_add c1 c2
    _ = 4 * ((q : ℝ) + 2) * (y * F ^ (q + 1)) + 4 * ((q : ℝ) + 2) ^ 2 * (y ^ 2 * F ^ q) := by ring
    _ ≤ 4 * ((q : ℝ) + 2) * (y ^ (q + 2) + F ^ (q + 2)) +
        4 * ((q : ℝ) + 2) ^ 2 * (y ^ (q + 2) + F ^ (q + 2)) := by gcongr
    _ = _ := by ring

/-! ## The bad event -/

/-- Off a measurable event of probability at most `3 N^{-(D−2)}`, the a priori bounds give
`|G_{v e_i}|, |G_{ii}| ≤ b + t` for all `i`, and `N⁻¹ ∑ᵢ |G_{v e_i}|² ≤ R₀`; here
`b = N^ε N^{2δ}`, `R₀ = N^ε N^{(C₀+1)δ} Ψ²` and `t` bounds `Π` entrywise. -/
private lemma diag_event {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN1 : 1 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hAH : A.IsHermitian) (hWs : ∀ ω, (W ω)ᵀ = W ω) (hWm : ∀ i j, Measurable fun ω => W ω i j)
    {z : ℂ} (hη0 : 0 < z.im) (v : Fin N → ℝ) (hv : testNorm v = 1) {C₀ δ ε D t : ℝ}
    (hPi : ∀ x y : Fin N → ℝ, ‖ent (piW A z) x y‖ ≤ t * testNorm x * testNorm y)
    (hr1 : ∀ v w : Fin N → ℝ, DomAt N ε (D - 1)
      (fun ω => ‖testBilin v (GW A (W ω) z - piW A z) w‖)
      (fun _ => (N : ℝ) ^ (2 * δ) * testNorm v * testNorm w))
    (hr2 : ∀ v : Fin N → ℝ, testNorm v = 1 → DomAt N ε D
      (fun ω => (ent (GW A (W ω) z) v v).im / (N * z.im))
      (fun _ => (N : ℝ) ^ ((C₀ + 1) * δ) * PsiW (specOf A) z ^ 2)) :
    ∃ Bad : Set Ω, MeasurableSet Bad ∧ (ℙ : Measure Ω).real Bad ≤ 3 * (N : ℝ) ^ (-(D - 2)) ∧
      ∀ ω ∉ Bad,
        (∀ i, ‖ent (GW A (W ω) z) v (eI i)‖ ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * 1 * 1) + t) ∧
        (∀ i, ‖GW A (W ω) z i i‖ ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * 1 * 1) + t) ∧
        (N : ℝ)⁻¹ * ∑ i, ‖ent (GW A (W ω) z) v (eI i)‖ ^ 2 ≤
          (N : ℝ) ^ ε * ((N : ℝ) ^ ((C₀ + 1) * δ) * PsiW (specOf A) z ^ 2) := by
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hvs : ∀ i : Fin N, testNorm (eI i) = 1 := fun i => diag_testNorm_eI i
  set Ea : Fin N → Set Ω := fun i => {ω | (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * testNorm v *
    testNorm (eI i)) < ‖testBilin v (GW A (W ω) z - piW A z) (eI i)‖} with hEa
  set Eb : Fin N → Set Ω := fun i => {ω | (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * testNorm (eI i) *
    testNorm (eI i)) < ‖testBilin (eI i) (GW A (W ω) z - piW A z) (eI i)‖} with hEb
  set Ec : Set Ω := {ω | (N : ℝ) ^ ε * ((N : ℝ) ^ ((C₀ + 1) * δ) * PsiW (specOf A) z ^ 2) <
    (ent (GW A (W ω) z) v v).im / (N * z.im)} with hEc
  have hmeasEa : ∀ i, MeasurableSet (Ea i) := fun i =>
    measurableSet_lt measurable_const
      (Measurable.norm (diag_measurable_entGP hWm A z v (eI i)))
  have hmeasEb : ∀ i, MeasurableSet (Eb i) := fun i =>
    measurableSet_lt measurable_const
      (Measurable.norm (diag_measurable_entGP hWm A z (eI i) (eI i)))
  have hmeasEc : MeasurableSet Ec := by
    refine measurableSet_lt measurable_const ?_
    exact (Complex.measurable_im.comp (diag_measurable_entG hWm A z v v)).div_const _
  have hD2 : D - 2 + 1 = D - 1 := by ring
  have hcard : ((Finset.univ : Finset (Fin N)).card : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
    simp
  have hPa : ℙ (⋃ i, Ea i) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 2))) := by
    refine le_trans (measure_mono ?_) (DomAt.measure_exists_lt (Finset.univ : Finset (Fin N))
      (N := N) (ε := ε) (D := D - 2) (C := 1) hN1 hcard
      (ξ := fun i ω => ‖testBilin v (GW A (W ω) z - piW A z) (eI i)‖)
      (ζ := fun i _ => (N : ℝ) ^ (2 * δ) * testNorm v * testNorm (eI i)) ?_)
    · intro ω hω
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hω
      exact ⟨i, Finset.mem_univ _, hi⟩
    · intro i _
      rw [hD2]
      exact hr1 v (eI i)
  have hPb : ℙ (⋃ i, Eb i) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 2))) := by
    refine le_trans (measure_mono ?_) (DomAt.measure_exists_lt (Finset.univ : Finset (Fin N))
      (N := N) (ε := ε) (D := D - 2) (C := 1) hN1 hcard
      (ξ := fun i ω => ‖testBilin (eI i) (GW A (W ω) z - piW A z) (eI i)‖)
      (ζ := fun i _ => (N : ℝ) ^ (2 * δ) * testNorm (eI i) * testNorm (eI i)) ?_)
    · intro ω hω
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hω
      exact ⟨i, Finset.mem_univ _, hi⟩
    · intro i _
      rw [hD2]
      exact hr1 (eI i) (eI i)
  have hPc : ℙ Ec ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 2))) :=
    le_trans (hr2 v hv) (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)))
  refine ⟨(⋃ i, Ea i) ∪ (⋃ i, Eb i) ∪ Ec,
    ((MeasurableSet.iUnion hmeasEa).union (MeasurableSet.iUnion hmeasEb)).union hmeasEc, ?_, ?_⟩
  · have h3 : ℙ ((⋃ i, Ea i) ∪ (⋃ i, Eb i) ∪ Ec) ≤
        ENNReal.ofReal (3 * (N : ℝ) ^ (-(D - 2))) := by
      have hx : 0 ≤ (N : ℝ) ^ (-(D - 2)) := Real.rpow_nonneg hNpos.le _
      calc ℙ ((⋃ i, Ea i) ∪ (⋃ i, Eb i) ∪ Ec) ≤ ℙ (⋃ i, Ea i) + ℙ (⋃ i, Eb i) + ℙ Ec :=
            (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
        _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 2))) + ENNReal.ofReal ((N : ℝ) ^ (-(D - 2))) +
              ENNReal.ofReal ((N : ℝ) ^ (-(D - 2))) := add_le_add (add_le_add hPa hPb) hPc
        _ = ENNReal.ofReal (3 * (N : ℝ) ^ (-(D - 2))) := by
            rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (add_nonneg hx hx) hx]
            congr 1; ring
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3
  · intro ω hω
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · have h1 : ω ∉ Ea i := fun h => hω (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, h⟩)))
      have h1' : ‖testBilin v (GW A (W ω) z - piW A z) (eI i)‖ ≤
          (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * testNorm v * testNorm (eI i)) := not_lt.1 h1
      rw [hv, hvs i] at h1'
      have hd : ent (GW A (W ω) z) v (eI i) =
          ent (GW A (W ω) z - piW A z) v (eI i) + ent (piW A z) v (eI i) := by
        rw [diag_ent_sub]; ring
      rw [hd]
      refine (norm_add_le _ _).trans ?_
      have h2 := hPi v (eI i)
      rw [hv, hvs i, mul_one, mul_one] at h2
      exact add_le_add h1' h2
    · have h1 : ω ∉ Eb i := fun h => hω (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, h⟩)))
      have h1' : ‖testBilin (eI i) (GW A (W ω) z - piW A z) (eI i)‖ ≤
          (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * testNorm (eI i) * testNorm (eI i)) := not_lt.1 h1
      rw [hvs i] at h1'
      have hd : ent (GW A (W ω) z) (eI i) (eI i) =
          ent (GW A (W ω) z - piW A z) (eI i) (eI i) + ent (piW A z) (eI i) (eI i) := by
        rw [diag_ent_sub]; ring
      rw [← ent_eI_eI (GW A (W ω) z) i i, hd]
      refine (norm_add_le _ _).trans ?_
      have h2 := hPi (eI i) (eI i)
      rw [hvs i, mul_one, mul_one] at h2
      exact add_le_add h1' h2
    · have h1 : ω ∉ Ec := fun h => hω (Or.inr h)
      have h1' : (ent (GW A (W ω) z) v v).im / (N * z.im) ≤
          (N : ℝ) ^ ε * ((N : ℝ) ^ ((C₀ + 1) * δ) * PsiW (specOf A) z ^ 2) := not_lt.1 h1
      rw [diag_ward hAH (hWs ω) hη0 v]
      calc (N : ℝ)⁻¹ * ((ent (GW A (W ω) z) v v).im / z.im)
          = (ent (GW A (W ω) z) v v).im / (N * z.im) := by
            field_simp
        _ ≤ _ := h1'

/-! ## Lemma 12.7: the diagonal second-order term -/

/-- The diagonal second-order term (the GOE/W variance mismatch on the diagonal). -/
theorem wig_coeff_diag (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (P : ModelClassW N) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N C P A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
          (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ ω, ‖fCoeff p (resCoeffW A (W ω) z v i i) 2‖ ≤
            K * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p + ∫ ω, FvW A (W ω) z v ^ p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  obtain ⟨N₁, hN₁⟩ := wig_rough_bound τ C C₀ δ (δ / 4) (dPrev (q + 2)) hτ hτ1 hδ hC₀ hC₀δ
    (by positivity)
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set Pq : ℝ := ((q : ℝ) + 2) + ((q : ℝ) + 2) ^ 2 with hPq
  set e : ℝ := 2 * (δ / 4) + 2 * δ with he
  have he0 : 0 < e := by positivity
  refine ⟨(4 * ((q : ℝ) + 2) + 4 * ((q : ℝ) + 2) ^ 2) +
    3 * Pq * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2), by positivity,
    max (max N₁ 2) (max ⌈τ⁻¹⌉₊ ⌈(τ⁻¹) ^ e⁻¹⌉₊), ?_⟩
  intro N hN A S P m hset hm hAm Ω _ _ W hW hP z hz v hv
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNτ : τ⁻¹ ≤ (N : ℝ) := by
    have h0 : ⌈τ⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast h0)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : 1 ≤ N := by omega
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hbN : τ⁻¹ ≤ (N : ℝ) ^ e := by
    have h0 : ⌈(τ⁻¹) ^ e⁻¹⌉₊ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have h1 : (τ⁻¹) ^ e⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h0)
    calc τ⁻¹ = ((τ⁻¹) ^ e⁻¹) ^ e := (Real.rpow_inv_rpow hτi.le he0.ne').symm
      _ ≤ (N : ℝ) ^ e := Real.rpow_le_rpow (Real.rpow_nonneg hτi.le _) h1 he0.le
  have hzS : z ∈ S := hz.1
  obtain ⟨hη0, hzE, hηlow, hηup⟩ := hset.domain.1 hzS
  obtain ⟨hr1, hr2⟩ := hN₁ N hN₁' A S P m hset hm hAm Ω W hW hP z hz
  have hAH : A.IsHermitian := hset.symmA
  have hWs : ∀ ω, (W ω)ᵀ = W ω := hW.symm
  have hWm : ∀ i j, Measurable fun ω => W ω i j := hW.measurable
  have hC0δ : 0 ≤ C₀ * δ := by nlinarith
  set η : ℝ := z.im with hη
  set y : ℝ := (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z with hy
  have hy2 : y ≤ 2 := diag_psi_small hN1 hC₀δ hC0δ (specOf A) ⟨hη0, hzE, hηlow, hηup⟩
  obtain ⟨hΨ0, hΨ2, hΨ3⟩ := diag_psi_facts hN1 (specOf A) hη0
  have hy0 : 0 ≤ y := mul_nonneg (Real.rpow_nonneg hNpos.le _) hΨ0
  -- the inverse of `η`
  have hηN : η⁻¹ ≤ N := by
    have h1 : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (N : ℝ)⁻¹ ≤ η := h1.trans hηlow
    calc η⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) h2
      _ = N := inv_inv _
  -- the lower bound `y ≥ τ / N`
  have hyτ : τ / N ≤ y := by
    have h1 : 1 ≤ (N : ℝ) ^ (C₀ * δ) := Real.one_le_rpow hNone hC0δ
    have h2 : τ / N ≤ 1 / (N * η) := by
      rw [div_le_div_iff₀ hNpos (by positivity)]
      have : η * τ ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hηup hτ.le
        rwa [inv_mul_cancel₀ hτ.ne'] at this
      nlinarith
    calc τ / N ≤ 1 / (N * η) := h2
      _ ≤ PsiW (specOf A) z := hΨ3
      _ ≤ y := le_mul_of_one_le_left hΨ0 h1
  -- test vectors
  have hvs : ∀ i : Fin N, testNorm (eI i) = 1 := fun i => diag_testNorm_eI i
  set ε : ℝ := 2 * (δ / 4) with hε
  set b : ℝ := (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * 1 * 1) with hb
  have hbe : b = (N : ℝ) ^ e := by
    rw [hb, he, Real.rpow_add hNpos]; ring
  have hτb : τ⁻¹ ≤ b := hbe ▸ hbN
  set B : ℝ := b + τ⁻¹ with hB
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hB2 : B ≤ 2 * b := by rw [hB]; linarith
  set R₀ : ℝ := (N : ℝ) ^ ε * ((N : ℝ) ^ ((C₀ + 1) * δ) * PsiW (specOf A) z ^ 2) with hR₀
  have hR0 : 0 ≤ R₀ := by rw [hR₀]; have := hΨ0; positivity
  -- exponent bookkeeping
  obtain ⟨hs1, hs2⟩ := diag_scalar (n := (N : ℝ)) (C₀ := C₀) (δ := δ)
    (Ψ := PsiW (specOf A) z) hNone hC₀ hδ
  have hs1' : b * R₀ ≤ y ^ 2 := hs1
  have hs2' : b ^ 2 * R₀ ≤ y ^ 2 := hs2
  have hBR : B * R₀ ≤ 4 * y := by
    calc B * R₀ ≤ (2 * b) * R₀ := mul_le_mul_of_nonneg_right hB2 hR0
      _ = 2 * (b * R₀) := by ring
      _ ≤ 2 * y ^ 2 := by linarith
      _ ≤ 4 * y := by
        have : y ^ 2 ≤ 2 * y := by
          rw [sq]
          nlinarith [mul_le_mul_of_nonneg_left hy2 hy0]
        linarith
  have hB2R : B ^ 2 * R₀ ≤ 4 * y ^ 2 := by
    have hB0 : 0 ≤ B := by rw [hB]; linarith
    calc B ^ 2 * R₀ ≤ (2 * b) ^ 2 * R₀ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB0 hB2 2) hR0
      _ = 4 * (b ^ 2 * R₀) := by ring
      _ ≤ 4 * y ^ 2 := by linarith
  have hηi : 0 < η⁻¹ := inv_pos.2 hη0
  have hg_det : ∀ ω i, ‖ent (GW A (W ω) z) v (eI i)‖ ≤ η⁻¹ := fun ω i => by
    have := diag_ent_le hAH (hWs ω) hη0 v (eI i)
    rwa [hv, hvs, mul_one, mul_one] at this
  have hG_det : ∀ ω i, ‖GW A (W ω) z i i‖ ≤ η⁻¹ := fun ω i => by
    have := diag_ent_le hAH (hWs ω) hη0 (eI i) (eI i)
    rw [ent_eI_eI, hvs, mul_one, mul_one] at this
    exact this
  have hPi : ∀ x y : Fin N → ℝ, ‖ent (piW A z) x y‖ ≤ τ⁻¹ * testNorm x * testNorm y :=
    fun x y => norm_piW_le hτ hAH hset.standing hzS x y
  have hF_det : ∀ ω, FvW A (W ω) z v ≤ η⁻¹ + τ⁻¹ := fun ω => by
    unfold FvW
    rw [diag_ent_sub]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · have := diag_ent_le hAH (hWs ω) hη0 v v
      rwa [hv, mul_one, mul_one] at this
    · have := hPi v v
      rwa [hv, mul_one, mul_one] at this
  have hF0 : ∀ ω, 0 ≤ FvW A (W ω) z v := fun ω => norm_nonneg _
  obtain ⟨Bad, hmBad, hβ, hgood⟩ := diag_event hN1 hAH hWs hWm hη0 v hv hPi hr1 hr2
  have hFmax : η⁻¹ + τ⁻¹ ≤ 2 * N := by linarith
  set Fmax : ℝ := η⁻¹ + τ⁻¹ with hFmaxdef
  have hFm0 : 0 ≤ Fmax := by positivity
  set Bmax : ℝ := ((q : ℝ) + 2) * (η⁻¹) ^ 3 * Fmax ^ (q + 1) +
    ((q : ℝ) + 2) ^ 2 * (η⁻¹) ^ 4 * Fmax ^ q with hBmax
  have hBmax0 : 0 ≤ Bmax := by rw [hBmax]; positivity
  have hfbad : ∀ i ω, ‖fCoeff (q + 2) (resCoeffW A (W ω) z v i i) 2‖ ≤ Bmax := fun i ω =>
    (diag_pt q hAH (hWs ω) hη0 v i).trans
      (diag_pt_bad q (hg_det ω i) (norm_nonneg _) (hG_det ω i) (norm_nonneg _) (hF0 ω)
        (hF_det ω))
  have hfgood : ∀ i, ∀ ω ∉ Bad, ‖fCoeff (q + 2) (resCoeffW A (W ω) z v i i) 2‖ ≤
      ‖ent (GW A (W ω) z) v (eI i)‖ ^ 2 * (((q : ℝ) + 2) * B * FvW A (W ω) z v ^ (q + 1) +
        ((q : ℝ) + 2) ^ 2 * B ^ 2 * FvW A (W ω) z v ^ q) := fun i ω hω =>
    (diag_pt q hAH (hWs ω) hη0 v i).trans
      (diag_pt_good q ((hgood ω hω).1 i) (norm_nonneg _) ((hgood ω hω).2.1 i) (hF0 ω))
  -- integrability of `F^p`
  have hFmeas : Measurable fun ω => FvW A (W ω) z v := diag_measurable_Fv hWm A z v
  have hFp : Integrable fun ω => FvW A (W ω) z v ^ (q + 2) :=
    Integrable.of_bound (hFmeas.pow_const _).aestronglyMeasurable (Fmax ^ (q + 2))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hF0 ω) _)]
        exact pow_le_pow_left₀ (hF0 ω) (hF_det ω) _)
  set K1 : ℝ := 4 * ((q : ℝ) + 2) + 4 * ((q : ℝ) + 2) ^ 2 with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set Ψf : Ω → ℝ := fun ω => K1 * (y ^ (q + 2) + FvW A (W ω) z v ^ (q + 2)) with hΨf
  have hΨi : Integrable Ψf := ((integrable_const (y ^ (q + 2))).add hFp).const_mul K1
  have hΨ0' : ∀ ω, 0 ≤ Ψf ω := fun ω => by
    have := hF0 ω
    simp only [hΨf]
    positivity
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hmain := diag_average (q := q) hN1
    (fun i ω => ‖fCoeff (q + 2) (resCoeffW A (W ω) z v i i) 2‖)
    (fun i ω => ‖ent (GW A (W ω) z) v (eI i)‖ ^ 2) (fun ω => FvW A (W ω) z v) Ψf Bad hmBad
    (fun i => ((diag_measurable_entG hWm A z v (eI i)).norm).pow_const 2) hFmeas
    (((q : ℝ) + 2) * B) (((q : ℝ) + 2) ^ 2 * B ^ 2) Bmax R₀ ((η⁻¹) ^ 2) Fmax
    (3 * (N : ℝ) ^ (-(dPrev (q + 2) - 2)))
    (by positivity) (by positivity) hBmax0
    (fun i ω => norm_nonneg _) (fun i ω => by positivity) hF0
    (fun i ω => pow_le_pow_left₀ (norm_nonneg _) (hg_det ω i) 2) hF_det hfbad
    (fun i ω hω => by simpa [mul_assoc] using hfgood i ω hω)
    (fun ω hω => (hgood ω hω).2.2) hΨi hΨ0'
    (fun ω => by simpa [mul_assoc] using diag_phi q hy0 (hF0 ω) hBR hB2R) hβ
  have hI : ∫ ω, Ψf ω = K1 * (y ^ (q + 2) + ∫ ω, FvW A (W ω) z v ^ (q + 2)) := by
    simp only [hΨf]
    rw [integral_const_mul, integral_add (integrable_const _) hFp, integral_const]
    simp
  have hInn : 0 ≤ ∫ ω, FvW A (W ω) z v ^ (q + 2) :=
    integral_nonneg fun ω => pow_nonneg (hF0 ω) _
  have hηN2 : η⁻¹ ≤ 2 * N := by linarith
  have hBm_le : Bmax ≤ (((q : ℝ) + 2) + ((q : ℝ) + 2) ^ 2) * (2 * (N : ℝ)) ^ (q + 4) := by
    have h1 : ((q : ℝ) + 2) * (η⁻¹) ^ 3 * Fmax ^ (q + 1) ≤
        ((q : ℝ) + 2) * (2 * (N : ℝ)) ^ 3 * (2 * (N : ℝ)) ^ (q + 1) := by gcongr
    have h2 : ((q : ℝ) + 2) ^ 2 * (η⁻¹) ^ 4 * Fmax ^ q ≤
        ((q : ℝ) + 2) ^ 2 * (2 * (N : ℝ)) ^ 4 * (2 * (N : ℝ)) ^ q := by gcongr
    calc Bmax ≤ ((q : ℝ) + 2) * (2 * (N : ℝ)) ^ 3 * (2 * (N : ℝ)) ^ (q + 1) +
          ((q : ℝ) + 2) ^ 2 * (2 * (N : ℝ)) ^ 4 * (2 * (N : ℝ)) ^ q := add_le_add h1 h2
      _ = _ := by ring
  have hbad := diag_bad_bound (n := (N : ℝ)) (τ := τ) (y := y) (q := q) hNone hτ hyτ hBm_le
  have hPq0 : 0 ≤ Pq := by rw [hPq]; positivity
  have hc : 0 ≤ 3 * Pq * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2) := by positivity
  refine hmain.trans ?_
  rw [hI]
  have hexp : (K1 + 3 * Pq * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2)) *
      (y ^ (q + 2) + ∫ ω, FvW A (W ω) z v ^ (q + 2)) =
      K1 * (y ^ (q + 2) + ∫ ω, FvW A (W ω) z v ^ (q + 2)) +
      (3 * Pq * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2)) * y ^ (q + 2) +
      (3 * Pq * 2 ^ (q + 4) * (τ⁻¹) ^ (q + 2)) * ∫ ω, FvW A (W ω) z v ^ (q + 2) := by ring
  rw [hexp]
  linarith [mul_nonneg hc hInn, hbad]

#print axioms Anisotropic.wig_coeff_diag

end Anisotropic
