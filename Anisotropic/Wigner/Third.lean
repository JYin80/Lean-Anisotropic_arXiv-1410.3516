import Anisotropic.Comparison.Ladder
import Anisotropic.Comparison.Props
import Anisotropic.Comparison.Words
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.Props
import Anisotropic.Wigner.RoughBound
import Anisotropic.Wigner.SelfConsistentII
import Anisotropic.Wigner.Words

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Lemma 12.7: the coefficient of order 3 (cases (a), (b)) -/

/-! ## The spectral form of `G^W` and its consequences -/

/-- A real symmetric `M` is `U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma thr_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
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
private lemma thr_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
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
private lemma thr_testNorm_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- `∑ₛ (Q v)ₛ² = ∑ₛ vₛ²` for `Qᵀ Q = 1`. -/
private lemma thr_sum_sq_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : ∑ s, (Q *ᵥ v) s ^ 2 = ∑ s, v s ^ 2 := by
  have h := thr_testNorm_orth hQ v
  unfold testNorm at h
  rwa [Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h

/-- The sandwich `⟨v, U D Uᵀ w⟩ = ∑ₖ dₖ (Uᵀ v)ₖ (Uᵀ w)ₖ`. -/
private lemma thr_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
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

/-- The spectral form of `G^W(z) = (W + A − z)⁻¹` for real symmetric `W + A`: a real orthogonal
`U` and eigenvalues `λ` with `G_{vw}(z) = ∑ₖ (λₖ − z)⁻¹ (Uᵀv)ₖ (Uᵀw)ₖ` for all `Im z > 0`. -/
private lemma thr_spectral {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) : ∃ (U : Matrix (Fin N) (Fin N) ℝ) (l : Fin N → ℝ), U * Uᵀ = 1 ∧
      Uᵀ * U = 1 ∧ ∀ z : ℂ, 0 < z.im → ∀ v w : Fin N → ℝ, ent (GW A Wm z) v w =
        ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ) := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := thr_eig_decomp (hW'.add hA)
  refine ⟨U, l, hUU, hUU', fun z hz v w => ?_⟩
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    thr_resolvent_eq hUU hUU' hMU hne
  rw [hG, thr_ent_sandwich]

/-- `|(λ − z)⁻¹| ≤ (Im z)⁻¹` for real `λ` and `Im z > 0`. -/
private lemma thr_norm_inv_le (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ hz ?_
  have h := Complex.abs_im_le_norm ((x : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at h
  exact h

/-- `G^W` is complex symmetric: `G_{vw} = G_{wv}`. -/
private lemma thr_G_symm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v w : Fin N → ℝ) :
    ent (GW A Wm z) v w = ent (GW A Wm z) w v := by
  obtain ⟨U, l, -, -, hG⟩ := thr_spectral hA hW
  rw [hG z hz, hG z hz]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm ((Uᵀ *ᵥ v) k)]

/-- `|G_{vw}| ≤ (Im z)⁻¹ |v| |w|`. -/
private lemma thr_G_norm_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v w : Fin N → ℝ) :
    ‖ent (GW A Wm z) v w‖ ≤ z.im⁻¹ * testNorm v * testNorm w := by
  obtain ⟨U, l, hUU, -, hG⟩ := thr_spectral hA hW
  have hQ : (Uᵀ)ᵀ * Uᵀ = 1 := by simpa using hUU
  rw [hG z hz]
  calc ‖∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ)‖
      ≤ ∑ k, ‖((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ v) k * (Uᵀ *ᵥ w) k : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k, z.im⁻¹ * (|(Uᵀ *ᵥ v) k| * |(Uᵀ *ᵥ w) k|) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (thr_norm_inv_le _ hz) (by positivity)
    _ = z.im⁻¹ * ∑ k, |(Uᵀ *ᵥ v) k| * |(Uᵀ *ᵥ w) k| := by rw [Finset.mul_sum]
    _ ≤ z.im⁻¹ * (testNorm (Uᵀ *ᵥ v) * testNorm (Uᵀ *ᵥ w)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hz.le)
        have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |(Uᵀ *ᵥ v) k|)
          (fun k => |(Uᵀ *ᵥ w) k|)
        simpa [testNorm, sq_abs] using h
    _ = z.im⁻¹ * testNorm v * testNorm w := by
        rw [thr_testNorm_orth hQ, thr_testNorm_orth hQ]
        ring

/-- The Ward identity `∑ₐ |G_{va}|² = Im G_{vv} / Im z`. -/
private lemma thr_ward {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) :
    ∑ a, ‖ent (GW A Wm z) v (eI a)‖ ^ 2 = (ent (GW A Wm z) v v).im / z.im := by
  obtain ⟨U, l, -, hUU', hG⟩ := thr_spectral hA hW
  set d : Fin N → ℂ := fun k => ((l k : ℂ) - z)⁻¹ with hd
  set c : Fin N → ℂ := fun k => d k * ((Uᵀ *ᵥ v) k : ℂ) with hc
  have hga : ∀ a, ent (GW A Wm z) v (eI a) = ∑ k, (U a k : ℂ) * c k := by
    intro a
    rw [hG z hz]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (Uᵀ *ᵥ eI a) k = U a k := by
      simp [mulVec, dotProduct, eI, Pi.single_apply, transpose_apply]
    rw [this, hc]
    push_cast
    ring
  have hre : ∀ a, (ent (GW A Wm z) v (eI a)).re = (U *ᵥ fun k => (c k).re) a := by
    intro a
    rw [hga, Complex.re_sum]
    simp [mulVec, dotProduct]
  have him : ∀ a, (ent (GW A Wm z) v (eI a)).im = (U *ᵥ fun k => (c k).im) a := by
    intro a
    rw [hga, Complex.im_sum]
    simp [mulVec, dotProduct]
  have h1 : ∑ a, ‖ent (GW A Wm z) v (eI a)‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
    have e : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := fun x => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [e, Finset.sum_add_distrib, hre, him]
    rw [thr_sum_sq_orth hUU', thr_sum_sq_orth hUU']
  have h2 : (ent (GW A Wm z) v v).im = z.im * ∑ k, ‖c k‖ ^ 2 := by
    rw [hG z hz, Complex.im_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : (l k : ℂ) - z ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    rw [Complex.im_mul_ofReal, hc]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hd]
    simp only
    rw [Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    field_simp
  rw [h1, h2]
  field_simp

/-! ## Bilinear forms in coordinates -/

/-- `⟨x, B y⟩ = ∑ₛ ∑ₜ xₛ Bₛₜ yₜ`. -/
private lemma thr_ent_eq {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- `⟨v, B eₐ⟩ = ∑ₛ vₛ B_{sa}`. -/
private lemma thr_ent_eI_right {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℝ)
    (a : Fin N) : ent B v (eI a) = ∑ s, (v s : ℂ) * B s a := by
  rw [thr_ent_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [eI]
  · intro b _ hb; simp [eI, hb]
  · simp

/-- `⟨eₐ, B w⟩ = ∑ₜ B_{at} wₜ`. -/
private lemma thr_ent_eI_left {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℝ)
    (a : Fin N) : ent B (eI a) w = ∑ t, B a t * (w t : ℂ) := by
  rw [thr_ent_eq, Finset.sum_eq_single a]
  · simp [eI]
  · intro b _ hb; simp [eI, hb]
  · simp

/-- `∑ₐ xₐ ⟨v, B eₐ⟩ = ⟨v, B x⟩`. -/
private lemma thr_sum_ent_eI {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (v x : Fin N → ℝ) :
    ∑ a, (x a : ℂ) * ent B v (eI a) = ent B v x := by
  simp only [thr_ent_eI_right]
  rw [thr_ent_eq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

/-- `∑ₐ xₐ ⟨eₐ, B w⟩ = ⟨x, B w⟩`. -/
private lemma thr_sum_ent_eI_left {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (w x : Fin N → ℝ) :
    ∑ a, (x a : ℂ) * ent B (eI a) w = ent B x w := by
  simp only [thr_ent_eI_left]
  rw [thr_ent_eq]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

/-- For a complex vector `c`, `⟨v, B c⟩ = ⟨v, B Re c⟩ + i ⟨v, B Im c⟩`. -/
private lemma thr_sum_cplx {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℝ)
    (c : Fin N → ℂ) :
    ∑ a, c a * ent B v (eI a) =
      ent B v (fun a => (c a).re) + Complex.I * ent B v (fun a => (c a).im) := by
  rw [← thr_sum_ent_eI, ← thr_sum_ent_eI, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [← Complex.re_add_im (c a)]
  ring

/-- If `|∑ᵢ xᵢ cᵢ| ≤ T |x|` for all real `x`, then `∑ᵢ |cᵢ|² ≤ 2 T²`. -/
private lemma thr_sum_sq_le {N : ℕ} {c : Fin N → ℂ} {T : ℝ}
    (h : ∀ x : Fin N → ℝ, ‖∑ i, (x i : ℂ) * c i‖ ≤ T * testNorm x) :
    ∑ i, ‖c i‖ ^ 2 ≤ 2 * T ^ 2 := by
  have key : ∀ x : Fin N → ℝ, ∑ i, x i ^ 2 ≤ ‖∑ i, (x i : ℂ) * c i‖ →
      ∑ i, x i ^ 2 ≤ T ^ 2 := by
    intro x hx
    have h1 := (h x).trans' hx
    have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hn : testNorm x ^ 2 = ∑ i, x i ^ 2 := by
      unfold testNorm; rw [Real.sq_sqrt hs]
    have hn0 : 0 ≤ testNorm x := Real.sqrt_nonneg _
    rw [← hn] at h1 ⊢
    nlinarith
  have hre : ∑ i, (c i).re ^ 2 ≤ T ^ 2 := by
    refine key _ ?_
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.re_sum]
    refine le_trans (le_of_eq ?_) (le_abs_self _)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_ofReal_mul]; ring
  have him : ∑ i, (c i).im ^ 2 ≤ T ^ 2 := by
    refine key _ ?_
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [Complex.im_sum]
    refine le_trans (le_of_eq ?_) (le_abs_self _)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.im_ofReal_mul]; ring
  have e : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := fun x => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [e, Finset.sum_add_distrib]
  linarith

/-- `|eₐ| = 1`. -/
private lemma thr_testNorm_eI {N : ℕ} (a : Fin N) : testNorm (eI a) = 1 := by
  simp [testNorm, eI, Pi.single_apply]

/-- The bounds on the rows and columns of `Π`: `∑_b |Π_{ab}|² ≤ 2 τ⁻²`, `∑_a |Π_{ab}|² ≤ 2 τ⁻²` and
`∑ₐ |Π_{va}|² ≤ 2 τ⁻²` for a unit `v`, from `‖Π‖ ≤ τ⁻¹`. -/
private lemma thr_pi_rows {N : ℕ} {T : ℝ} {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : ∀ x y : Fin N → ℝ, ‖testBilin x P y‖ ≤ T * testNorm x * testNorm y)
    (v : Fin N → ℝ) (hv : testNorm v = 1) :
    (∀ a, ∑ b, ‖P a b‖ ^ 2 ≤ 2 * T ^ 2) ∧ (∀ b, ∑ a, ‖P a b‖ ^ 2 ≤ 2 * T ^ 2) ∧
      ∑ a, ‖ent P v (eI a)‖ ^ 2 ≤ 2 * T ^ 2 := by
  refine ⟨fun a => ?_, fun b => ?_, ?_⟩
  · refine thr_sum_sq_le fun x => ?_
    have e : ∑ i, (x i : ℂ) * P a i = ent P (eI a) x := by
      rw [← thr_sum_ent_eI]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ent_eI_eI]
    rw [e]
    have := hP (eI a) x
    rwa [thr_testNorm_eI, mul_one] at this
  · refine thr_sum_sq_le fun x => ?_
    have e : ∑ i, (x i : ℂ) * P i b = ent P x (eI b) := by
      rw [← thr_sum_ent_eI_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ent_eI_eI]
    rw [e]
    have := hP x (eI b)
    rwa [thr_testNorm_eI, mul_one] at this
  · refine thr_sum_sq_le fun x => ?_
    rw [thr_sum_ent_eI]
    have := hP v x
    rwa [hv, mul_one] at this

/-! ## The coefficients `a_k`, `k ≤ 3`, along a symmetric entry (§12.2) -/

/-- The symmetric direction `E_{ij} + E_{ji}`, with both terms kept also for `i = j`. -/
private def thrD {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun s u => (if s = i ∧ u = j then 1 else 0) + (if s = j ∧ u = i then 1 else 0)

/-- `λ_{ij} = 1` for `i ≠ j` and `λ_{ii} = 1/2`, so that `Δ = λ_{ij} (E_{ij} + E_{ji})`. -/
private def thrLam {N : ℕ} (i j : Fin N) : ℝ := if i = j then 1 / 2 else 1

private lemma thr_deltaW_eq {N : ℕ} (i j : Fin N) :
    deltaW i j = ((thrLam i j : ℝ) : ℂ) • thrD i j := by
  ext s u
  rw [Matrix.smul_apply, smul_eq_mul]
  simp only [deltaW, thrD, thrLam]
  by_cases hij : i = j
  · subst hij
    by_cases h : s = i ∧ u = i
    · simp only [h, and_self, or_self, ite_true]; norm_num
    · simp only [h, or_self, ite_false]; simp
  · by_cases h1 : s = i ∧ u = j
    · have h2 : ¬ (s = j ∧ u = i) := fun h => hij (h1.1.symm.trans h.1)
      simp [h1, hij]
    · by_cases h2 : s = j ∧ u = i
      · simp [h2, hij]
      · simp [h1, h2]

/-- `(X (E_{ij} + E_{ji}) Y)_{st} = X_{si} Y_{jt} + X_{sj} Y_{it}`. -/
private lemma thr_mul_D_mul {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i j s t : Fin N) :
    (X * thrD i j * Y) s t = X s i * Y j t + X s j * Y i t := by
  have h1 : ∀ u, (X * thrD i j) s u =
      (if u = j then X s i else 0) + (if u = i then X s j else 0) := by
    intro u
    simp only [Matrix.mul_apply, thrD, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single i]
      · by_cases hu : u = j <;> simp [hu]
      · intro b _ hb; simp [hb]
      · simp
    · rw [Finset.sum_eq_single j]
      · by_cases hu : u = i <;> simp [hu]
      · intro b _ hb; simp [hb]
      · simp
  rw [Matrix.mul_apply]
  simp only [h1, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `⟨x, X (E_{ij} + E_{ji}) Y y⟩ = ⟨x, X eᵢ⟩ ⟨eⱼ, Y y⟩ + ⟨x, X eⱼ⟩ ⟨eᵢ, Y y⟩`. -/
private lemma thr_ent_mul_D_mul {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (x y : Fin N → ℝ) :
    ent (X * thrD i j * Y) x y =
      ent X x (eI i) * ent Y (eI j) y + ent X x (eI j) * ent Y (eI i) y := by
  rw [thr_ent_eI_right X x i, thr_ent_eI_left Y y j, thr_ent_eI_right X x j,
    thr_ent_eI_left Y y i, thr_ent_eq]
  simp only [thr_mul_D_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The rescaled coefficients `ã_k = λ_{ij}^{−k} a_k`, `k ≤ 3`, in terms of `g_a = G_{va}`,
`G_{ab}` and `a_0 = (G − Π)_{vv}` (the three words of §12.2 for a symmetric entry). -/
private def thrA {N : ℕ} (a0 : ℂ) (g : Fin N → ℂ) (Gm : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) : ℕ → ℂ
  | 0 => a0
  | 1 => -2 * g i * g j
  | 2 => g j ^ 2 * Gm i i + 2 * g i * g j * Gm i j + g i ^ 2 * Gm j j
  | 3 => -2 * (g j * Gm i i + g i * Gm i j) * (g j * Gm i j + g i * Gm j j)
  | _ => 0

/-- `a_k = λ_{ij}^k ã_k` for `k ≤ 3`. -/
private lemma thr_resCoeffW_eq {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i j : Fin N) {k : ℕ}
    (hk : k ≤ 3) :
    resCoeffW A Wm z v i j k = ((thrLam i j : ℝ) : ℂ) ^ k *
      thrA (ent (GW A Wm z - piW A z) v v) (fun a => ent (GW A Wm z) v (eI a)) (GW A Wm z)
        i j k := by
  set G := GW A Wm z with hG
  set c : ℂ := ((thrLam i j : ℝ) : ℂ) with hc
  have hsym : ∀ x y, ent G x y = ent G y x := fun x y => thr_G_symm hA hW hz x y
  have hGij : ∀ a b, G a b = ent G (eI a) (eI b) := fun a b => (ent_eI_eI G a b).symm
  have hpow : ∀ n : ℕ, G * (deltaW i j * G) ^ n = c ^ n • (G * (thrD i j * G) ^ n) := by
    intro n
    rw [thr_deltaW_eq, smul_mul_assoc, smul_pow, Matrix.mul_smul]
  have hsmul : ∀ (d : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) x y, ent (d • M) x y = d * ent M x y := by
    intro d M x y
    simp [ent, smul_mulVec, dotProduct_smul]
  have h1 : ent (G * thrD i j * G) v v =
      2 * ent G v (eI i) * ent G v (eI j) := by
    rw [thr_ent_mul_D_mul, hsym (eI j) v, hsym (eI i) v]; ring
  have hv1 : ∀ a, ent (G * thrD i j * G) v (eI a) =
      ent G v (eI i) * G j a + ent G v (eI j) * G i a := by
    intro a; rw [thr_ent_mul_D_mul, hGij j a, hGij i a]
  have hji : G j i = G i j := by rw [hGij, hGij i j, hsym]
  have hres : ∀ n : ℕ, 0 < n → resCoeffW A Wm z v i j n =
      (-1) ^ n * (c ^ n * ent (G * (thrD i j * G) ^ n) v v) := by
    intro n hn
    have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.1 hn
    rw [resCoeffW, ← hG, hpow]
    simp only [hn0, ↓reduceIte, sub_zero, hsmul]
  interval_cases k
  · simp [resCoeffW, thrA, ← hG]
  · have e : G * (thrD i j * G) ^ 1 = G * thrD i j * G := by
      simp only [pow_one, Matrix.mul_assoc]
    rw [hres 1 (by norm_num), e, h1]
    simp only [thrA]; ring
  · have e : G * (thrD i j * G) ^ 2 = G * thrD i j * G * thrD i j * G := by
      simp only [pow_two, Matrix.mul_assoc]
    rw [hres 2 (by norm_num), e, thr_ent_mul_D_mul, hv1, hv1,
      hsym (eI j) v, hsym (eI i) v, hji]
    simp only [thrA]; ring
  · have e : G * (thrD i j * G) ^ 3 = G * thrD i j * G * thrD i j * G * thrD i j * G := by
      simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
    have hv2 : ∀ a, ent (G * thrD i j * G * thrD i j * G) v (eI a) =
        (ent G v (eI i) * G j i + ent G v (eI j) * G i i) * G j a +
        (ent G v (eI i) * G j j + ent G v (eI j) * G i j) * G i a := by
      intro a; rw [thr_ent_mul_D_mul, hv1, hv1, hGij j a, hGij i a]
    rw [hres 3 (by norm_num), e, thr_ent_mul_D_mul, hv2, hv2,
      hsym (eI j) v, hsym (eI i) v, hji]
    simp only [thrA]; ring

/-- Rescaling the coefficients by `λ^k` rescales the order-`n` coefficient of `F_v^p` by `λ^n`. -/
private lemma thr_fCoeff_scale (p n : ℕ) {a b : ℕ → ℂ} (c : ℝ)
    (h : ∀ k ≤ n, a k = (c : ℂ) ^ k * b k) :
    fCoeff p a n = (c : ℂ) ^ n * fCoeff p b n := by
  unfold fCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hκ
  have hle : ∀ r, κ r ≤ n := fun r => by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ r)
    omega
  have e : ∀ r : Fin p, (if (r : ℕ) < p / 2 then a (κ r) else starRingEnd ℂ (a (κ r))) =
      (c : ℂ) ^ κ r * (if (r : ℕ) < p / 2 then b (κ r) else starRingEnd ℂ (b (κ r))) := by
    intro r
    rw [h _ (hle r)]
    split_ifs
    · rfl
    · rw [map_mul, map_pow, Complex.conj_ofReal]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hκ]

/-! ## The order-3 coefficient of `F_v^p` by the number of nonzero orders -/

/-- `f` is the identity or complex conjugation. -/
private def thrSel (f : ℂ → ℂ) : Prop := (∀ x, f x = x) ∨ ∀ x, f x = starRingEnd ℂ x

private lemma thrSel_norm {f : ℂ → ℂ} (hf : thrSel f) (x : ℂ) : ‖f x‖ = ‖x‖ := by
  rcases hf with h | h <;> simp [h]

/-- `x^a y^b ≤ x^{a+b} + y^{a+b}` for `x, y ≥ 0`. -/
private lemma thr_pow_mul_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (a b : ℕ) :
    x ^ a * y ^ b ≤ x ^ (a + b) + y ^ (a + b) := by
  rcases le_total x y with h | h
  · calc x ^ a * y ^ b ≤ y ^ a * y ^ b :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx h a) (pow_nonneg hy b)
      _ = y ^ (a + b) := (pow_add y a b).symm
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg hx _)
  · calc x ^ a * y ^ b ≤ x ^ a * x ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy h b) (pow_nonneg hx a)
      _ = x ^ (a + b) := (pow_add x a b).symm
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hy _)

/-- The order-3 coefficient summed against weights: if the sums with exactly one nonzero order
(`a_3`), two (`a_2 a_1`) and three (`a_1 a_1 a_1`) are bounded by `M X`, `M X²`, `M X³`, then
`|∑_α w_α f_3(α)| ≤ #tuples · M (F^p + X^p)` with `F = |a_0|`. -/
private lemma thr_fCoeff_three_le {ι : Type*} [Fintype ι] (p : ℕ) (b : ι → ℕ → ℂ) (a0 : ℂ)
    (hb0 : ∀ α, b α 0 = a0) (w : ι → ℂ) {M X : ℝ} (hM : 0 ≤ M) (hX : 0 ≤ X)
    (h3 : ∀ f, thrSel f → ‖∑ α, w α * f (b α 3)‖ ≤ M * X)
    (h21 : ∀ f f', thrSel f → thrSel f' → ‖∑ α, w α * (f (b α 2) * f' (b α 1))‖ ≤ M * X ^ 2)
    (h111 : ∀ f f' f'', thrSel f → thrSel f' → thrSel f'' →
      ‖∑ α, w α * (f (b α 1) * (f' (b α 1) * f'' (b α 1)))‖ ≤ M * X ^ 3) :
    ‖∑ α, w α * fCoeff p (b α) 3‖ ≤
      ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) * (M * (‖a0‖ ^ p + X ^ p)) := by
  set sel : Fin p → ℂ → ℂ := fun r x => if (r : ℕ) < p / 2 then x else starRingEnd ℂ x
    with hsel
  have hselS : ∀ r, thrSel (sel r) := by
    intro r
    by_cases h : (r : ℕ) < p / 2
    · left; intro x; simp [hsel, h]
    · right; intro x; simp [hsel, h]
  have hsum : ∑ α, w α * fCoeff p (b α) 3 =
      ∑ κ ∈ Finset.Nat.antidiagonalTuple p 3, ∑ α, w α * ∏ r, sel r (b α (κ r)) := by
    unfold fCoeff
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun κ hκ => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hκ
  set Z := Finset.univ.filter fun r : Fin p => κ r = 0 with hZ
  set R := Finset.univ.filter fun r : Fin p => κ r ≠ 0 with hR
  have hsplit : ∀ α, ∏ r, sel r (b α (κ r)) =
      (∏ r ∈ Z, sel r a0) * ∏ r ∈ R, sel r (b α (κ r)) := by
    intro α
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun r : Fin p => κ r = 0]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.1 hr).2, hb0]
  have hfac : ∑ α, w α * ∏ r, sel r (b α (κ r)) =
      (∏ r ∈ Z, sel r a0) * ∑ α, w α * ∏ r ∈ R, sel r (b α (κ r)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hsplit]; ring
  have hnZ : ‖∏ r ∈ Z, sel r a0‖ = ‖a0‖ ^ Z.card := by
    rw [norm_prod]
    simp [thrSel_norm (hselS _)]
  have hcard : Z.card + R.card = p := by
    rw [hZ, hR, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have hRsum : ∑ r ∈ R, κ r = 3 := by
    rw [hR, Finset.sum_filter_ne_zero, hκ]
  have hRle : R.card ≤ 3 := by
    have : ∑ r ∈ R, 1 ≤ ∑ r ∈ R, κ r := Finset.sum_le_sum fun r hr => by
      have := (Finset.mem_filter.1 hr).2; omega
    simpa [hRsum] using this
  have hpos : ∀ r ∈ R, 1 ≤ κ r := fun r hr => by
    have := (Finset.mem_filter.1 hr).2; omega
  have hmain : ‖∑ α, w α * ∏ r ∈ R, sel r (b α (κ r))‖ ≤ M * X ^ R.card := by
    interval_cases hc : R.card
    · exfalso
      rw [Finset.card_eq_zero] at hc
      rw [hc] at hRsum; simp at hRsum
    · obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hc
      rw [hr] at hRsum
      simp only [Finset.sum_singleton] at hRsum
      simp only [hr, Finset.prod_singleton, hRsum, pow_one]
      exact h3 _ (hselS r)
    · obtain ⟨r1, r2, h12, hr⟩ := Finset.card_eq_two.1 hc
      have h1 := hpos r1 (by rw [hr]; simp)
      have h2 := hpos r2 (by rw [hr]; simp)
      rw [hr, Finset.sum_pair h12] at hRsum
      simp only [hr, Finset.prod_pair h12]
      rcases (show (κ r1 = 2 ∧ κ r2 = 1) ∨ (κ r1 = 1 ∧ κ r2 = 2) by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact h21 _ _ (hselS r1) (hselS r2)
      · rw [e1, e2]
        simp only [mul_comm (sel r1 _) (sel r2 _)]
        exact h21 _ _ (hselS r2) (hselS r1)
    · obtain ⟨r1, r2, r3, h12, h13, h23, hr⟩ := Finset.card_eq_three.1 hc
      have h1 := hpos r1 (by rw [hr]; simp)
      have h2 := hpos r2 (by rw [hr]; simp)
      have h3' := hpos r3 (by rw [hr]; simp)
      have hsum3 : κ r1 + (κ r2 + κ r3) = 3 := by
        rw [hr, Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23] at hRsum
        exact hRsum
      have e1 : κ r1 = 1 := by omega
      have e2 : κ r2 = 1 := by omega
      have e3 : κ r3 = 1 := by omega
      simp only [hr, Finset.prod_insert (show r1 ∉ ({r2, r3} : Finset (Fin p)) by simp [h12, h13]),
        Finset.prod_pair h23, e1, e2, e3]
      exact h111 _ _ _ (hselS r1) (hselS r2) (hselS r3)
  rw [hfac, norm_mul, hnZ]
  calc ‖a0‖ ^ Z.card * ‖∑ α, w α * ∏ r ∈ R, sel r (b α (κ r))‖
      ≤ ‖a0‖ ^ Z.card * (M * X ^ R.card) :=
        mul_le_mul_of_nonneg_left hmain (pow_nonneg (norm_nonneg _) _)
    _ = M * (‖a0‖ ^ Z.card * X ^ R.card) := by ring
    _ ≤ M * (‖a0‖ ^ p + X ^ p) := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        have := thr_pow_mul_pow_le (norm_nonneg a0) hX Z.card R.card
        rwa [hcard] at this

/-! ## Deterministic bounds on the good event -/

/-- The bounds available on the good event, in coordinates: `g_a = G_{va}`, `pv_a = Π_{va}`,
`T = τ⁻¹`, `ρ` the loss in `|G − Π| ≺ 1`, `φ` the loss in `|G − Π| ≺ Φ`, and
`∑ₐ |G_{va}|² ≤ N σ²` (the Ward identity together with Lemma 12.6 (ii)). -/
private structure ThrHyp (N : ℕ) (g pv : Fin N → ℂ) (Gm Pm : Matrix (Fin N) (Fin N) ℂ)
    (T ρ φ σ : ℝ) : Prop where
  hT : 1 ≤ T
  hρ : 1 ≤ ρ
  hφ : 0 ≤ φ
  hσ : 0 ≤ σ
  hP : ∀ a b, ‖Pm a b‖ ≤ T
  hProw : ∀ a, ∑ b, ‖Pm a b‖ ^ 2 ≤ 2 * T ^ 2
  hPcol : ∀ b, ∑ a, ‖Pm a b‖ ^ 2 ≤ 2 * T ^ 2
  hpv : ∀ a, ‖pv a‖ ≤ T
  hpv2 : ∑ a, ‖pv a‖ ^ 2 ≤ 2 * T ^ 2
  hGρ : ∀ a b, ‖Gm a b - Pm a b‖ ≤ ρ
  hGφ : ∀ a b, ‖Gm a b - Pm a b‖ ≤ φ
  hgρ : ∀ a, ‖g a - pv a‖ ≤ ρ
  hgφ : ∀ a, ‖g a - pv a‖ ≤ φ
  hS2 : ∑ a, ‖g a‖ ^ 2 ≤ N * σ ^ 2

/-- The cancellation bounds: sums `∑ᵢ cᵢ G_{vi}` against the deterministic vectors built from
the weights `t` and the diagonal of `Π`. -/
private structure ThrCan (N : ℕ) (g : Fin N → ℂ) (Pm : Matrix (Fin N) (Fin N) ℂ)
    (t : Fin N → Fin N → ℂ) (B : ℝ) : Prop where
  hA : ∀ k, ‖∑ i, t i k * Pm i i * Pm k k * g i‖ ≤ B
  hB : ∀ k, ‖∑ i, t i k * Pm i i * g i‖ ≤ B
  hB' : ∀ k, ‖∑ i, starRingEnd ℂ (t i k * Pm i i) * g i‖ ≤ B
  hC : ∀ k, ‖∑ j, t k j * Pm j j * g j‖ ≤ B
  hC' : ∀ k, ‖∑ j, starRingEnd ℂ (t k j * Pm j j) * g j‖ ≤ B

/-- `∑ₐ |fₐ| ≤ √N (∑ₐ |fₐ|²)^{1/2}`. -/
private lemma thr_sum_norm_le {N : ℕ} (f : Fin N → ℂ) :
    ∑ a, ‖f a‖ ≤ √(N : ℝ) * √(∑ a, ‖f a‖ ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) (fun a => ‖f a‖)
  simpa using h

/-- The weighted triangle inequality `|∑ᵢⱼ tᵢⱼ Xᵢⱼ| ≤ ∑ᵢⱼ |Xᵢⱼ|` for `|tᵢⱼ| ≤ 1`. -/
private lemma thr_tri {N : ℕ} {t : Fin N → Fin N → ℂ} (ht : ∀ i j, ‖t i j‖ ≤ 1)
    (X : Fin N → Fin N → ℂ) : ‖∑ i, ∑ j, t i j * X i j‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ht i j)

namespace ThrHyp

variable {N : ℕ} {g pv : Fin N → ℂ} {Gm Pm : Matrix (Fin N) (Fin N) ℂ} {T ρ φ σ : ℝ}

private lemma g_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a : Fin N) : ‖g a‖ ≤ 2 * T * ρ := by
  have h1 : ‖g a‖ ≤ ‖pv a‖ + ‖g a - pv a‖ := by
    have := norm_add_le (pv a) (g a - pv a); simpa using this
  have := h.hpv a; have := h.hgρ a; have := h.hT; have := h.hρ
  nlinarith

private lemma G_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a b : Fin N) : ‖Gm a b‖ ≤ 2 * T * ρ := by
  have h1 : ‖Gm a b‖ ≤ ‖Pm a b‖ + ‖Gm a b - Pm a b‖ := by
    have := norm_add_le (Pm a b) (Gm a b - Pm a b); simpa using this
  have := h.hP a b; have := h.hGρ a b; have := h.hT; have := h.hρ
  nlinarith

private lemma S1_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) : ∑ a, ‖g a‖ ≤ N * σ := by
  refine (thr_sum_norm_le g).trans ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc √(N : ℝ) * √(∑ a, ‖g a‖ ^ 2) ≤ √(N : ℝ) * √(N * σ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h.hS2) (Real.sqrt_nonneg _)
    _ = N * σ := by
        rw [Real.sqrt_mul hN, Real.sqrt_sq h.hσ, ← mul_assoc, Real.mul_self_sqrt hN]

private lemma col_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (b : Fin N) :
    ∑ a, ‖Pm a b‖ ≤ 2 * T * √(N : ℝ) := by
  refine (thr_sum_norm_le (fun a => Pm a b)).trans ?_
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have : √(∑ a, ‖Pm a b‖ ^ 2) ≤ 2 * T := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [h.hPcol b]
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

private lemma row_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a : Fin N) :
    ∑ b, ‖Pm a b‖ ≤ 2 * T * √(N : ℝ) := by
  refine (thr_sum_norm_le (fun b => Pm a b)).trans ?_
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have : √(∑ b, ‖Pm a b‖ ^ 2) ≤ 2 * T := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [h.hProw a]
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

/-- `|G_{aa} G_{bc} − Π_{aa} Π_{bc}| ≤ 3 T ρ φ`. -/
private lemma prod_sub_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a b c d : Fin N) :
    ‖Gm a b * Gm c d - Pm a b * Pm c d‖ ≤ 3 * T * ρ * φ := by
  have e : Gm a b * Gm c d - Pm a b * Pm c d =
      Gm a b * (Gm c d - Pm c d) + (Gm a b - Pm a b) * Pm c d := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := h.G_le a b; have h2 := h.hGφ c d; have h3 := h.hGφ a b; have h4 := h.hP c d
  have := h.hT; have := h.hρ; have := h.hφ
  have h5 : ‖Gm a b‖ * ‖Gm c d - Pm c d‖ ≤ 2 * T * ρ * φ :=
    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have h6 : ‖Gm a b - Pm a b‖ * ‖Pm c d‖ ≤ φ * T :=
    mul_le_mul h3 h4 (norm_nonneg _) h.hφ
  have h7 : T * φ * 1 ≤ T * φ * ρ :=
    mul_le_mul_of_nonneg_left h.hρ (mul_nonneg (by linarith [h.hT]) h.hφ)
  linarith

/-- `|G_{aa}| |G_{bc}| ≤ T |Π_{bc}| + 3 T ρ φ`. -/
private lemma prod_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a b c : Fin N) :
    ‖Gm a a * Gm b c‖ ≤ T * ‖Pm b c‖ + 3 * T * ρ * φ := by
  have e : Gm a a * Gm b c = Pm a a * Pm b c + (Gm a a * Gm b c - Pm a a * Pm b c) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have := h.prod_sub_le a a b c
  have := mul_le_mul_of_nonneg_right (h.hP a a) (norm_nonneg (Pm b c))
  linarith

/-- `|G_{ab}|² ≤ 2 |Π_{ab}|² + 2 ρ φ`. -/
private lemma sq_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a b : Fin N) :
    ‖Gm a b‖ ^ 2 ≤ 2 * ‖Pm a b‖ ^ 2 + 2 * ρ * φ := by
  have h1 : ‖Gm a b‖ ≤ ‖Pm a b‖ + ‖Gm a b - Pm a b‖ := by
    have := norm_add_le (Pm a b) (Gm a b - Pm a b); simpa using this
  have h2 := h.hGρ a b; have h3 := h.hGφ a b
  have h4 : ‖Gm a b - Pm a b‖ ^ 2 ≤ ρ * φ :=
    (sq _).trans_le (mul_le_mul h2 h3 (norm_nonneg _) (by linarith [h.hρ]))
  have h5 : ‖Gm a b‖ ^ 2 ≤ (‖Pm a b‖ + ‖Gm a b - Pm a b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖Pm a b‖ - ‖Gm a b - Pm a b‖)]

private lemma cube_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) :
    ∑ a, ‖g a‖ ^ 3 ≤ 2 * T * ρ * (N * σ ^ 2) := by
  calc ∑ a, ‖g a‖ ^ 3 = ∑ a, ‖g a‖ * ‖g a‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => by ring
    _ ≤ ∑ a, 2 * T * ρ * ‖g a‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h.g_le a) (sq_nonneg _)
    _ = 2 * T * ρ * ∑ a, ‖g a‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * T * ρ * (N * σ ^ 2) :=
        mul_le_mul_of_nonneg_left h.hS2 (by have := h.hT; have := h.hρ; positivity)

end ThrHyp

namespace ThrHyp

variable {N : ℕ} {g pv : Fin N → ℂ} {Gm Pm : Matrix (Fin N) (Fin N) ℂ} {T ρ φ σ : ℝ}

/-- `∑ᵢⱼ c aⱼ = N c ∑ⱼ aⱼ` and `∑ᵢⱼ c aᵢ = N c ∑ᵢ aᵢ`. -/
private lemma thr_dsum_const_left {N : ℕ} (c : ℝ) (a : Fin N → ℝ) :
    ∑ _i : Fin N, ∑ j, c * a j = N * c * ∑ j, a j := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma thr_dsum_const_right {N : ℕ} (c : ℝ) (a : Fin N → ℝ) :
    ∑ i, ∑ _j : Fin N, c * a i = N * c * ∑ i, a i := by
  rw [Finset.sum_comm]; exact thr_dsum_const_left c a

/-- `∑ᵢⱼ |g_j|² |G_{ii} G_{ij}| ≤ 2T² √N · N σ² + 3Tρφ N · N σ²`. -/
private lemma sumX1_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) :
    ∑ i, ∑ j, ‖g j ^ 2 * (Gm i i * Gm i j)‖ ≤
      2 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) + 3 * T * ρ * φ * N * (N * σ ^ 2) := by
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have hc0 : 0 ≤ 3 * T * ρ * φ := by have := h.hρ; have := h.hφ; positivity
  have p1 : ∑ i, ∑ j, ‖g j ^ 2 * (Gm i i * Gm i j)‖ ≤
      ∑ i, ∑ j, T * ‖g j‖ ^ 2 * ‖Pm i j‖ + ∑ _i : Fin N, ∑ j, 3 * T * ρ * φ * ‖g j‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_pow]
    have := mul_le_mul_of_nonneg_left (h.prod_le i i j) (sq_nonneg ‖g j‖)
    linarith
  have p2 : ∑ i, ∑ j, T * ‖g j‖ ^ 2 * ‖Pm i j‖ ≤ 2 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, T * ‖g j‖ ^ 2 * ‖Pm i j‖ = ∑ j, T * ‖g j‖ ^ 2 * ∑ i, ‖Pm i j‖ := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ j, T * ‖g j‖ ^ 2 * (2 * T * √(N : ℝ)) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h.col_le j) (by positivity)
      _ = 2 * T ^ 2 * √(N : ℝ) * ∑ j, ‖g j‖ ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 2 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) :=
          mul_le_mul_of_nonneg_left h.hS2 (by positivity)
  have p3 : ∑ _i : Fin N, ∑ j, 3 * T * ρ * φ * ‖g j‖ ^ 2 ≤ 3 * T * ρ * φ * N * (N * σ ^ 2) := by
    rw [thr_dsum_const_left]
    have := mul_le_mul_of_nonneg_left h.hS2 (mul_nonneg (Nat.cast_nonneg N) hc0)
    linarith
  linarith

/-- `∑ᵢⱼ |g_i|² |G_{ij} G_{jj}| ≤ 2T² √N · N σ² + 3Tρφ N · N σ²`. -/
private lemma sumX4_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) :
    ∑ i, ∑ j, ‖g i ^ 2 * (Gm i j * Gm j j)‖ ≤
      2 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) + 3 * T * ρ * φ * N * (N * σ ^ 2) := by
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have hc0 : 0 ≤ 3 * T * ρ * φ := by have := h.hρ; have := h.hφ; positivity
  have p1 : ∑ i, ∑ j, ‖g i ^ 2 * (Gm i j * Gm j j)‖ ≤
      ∑ i, ∑ j, T * ‖g i‖ ^ 2 * ‖Pm i j‖ + ∑ i, ∑ _j : Fin N, 3 * T * ρ * φ * ‖g i‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_pow, mul_comm (Gm i j)]
    have := mul_le_mul_of_nonneg_left (h.prod_le j i j) (sq_nonneg ‖g i‖)
    linarith
  have p2 : ∑ i, ∑ j, T * ‖g i‖ ^ 2 * ‖Pm i j‖ ≤ 2 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) := by
    calc ∑ i, ∑ j, T * ‖g i‖ ^ 2 * ‖Pm i j‖ = ∑ i, T * ‖g i‖ ^ 2 * ∑ j, ‖Pm i j‖ := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ i, T * ‖g i‖ ^ 2 * (2 * T * √(N : ℝ)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h.row_le i) (by positivity)
      _ = 2 * T ^ 2 * √(N : ℝ) * ∑ i, ‖g i‖ ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 2 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) :=
          mul_le_mul_of_nonneg_left h.hS2 (by positivity)
  have p3 : ∑ i, ∑ _j : Fin N, 3 * T * ρ * φ * ‖g i‖ ^ 2 ≤ 3 * T * ρ * φ * N * (N * σ ^ 2) := by
    rw [thr_dsum_const_right]
    have := mul_le_mul_of_nonneg_left h.hS2 (mul_nonneg (Nat.cast_nonneg N) hc0)
    linarith
  linarith

/-- `∑ᵢⱼ |g_i| |g_j| |G_{ij}|² ≤ 8T³ρ Nσ + 2ρφ (Nσ)²`. -/
private lemma sumX3_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) :
    ∑ i, ∑ j, ‖g i * g j * Gm i j ^ 2‖ ≤
      8 * T ^ 3 * ρ * (N * σ) + 2 * ρ * φ * (N * σ) ^ 2 := by
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have hρ0 : 0 ≤ ρ := by linarith [h.hρ]
  have hS1 := h.S1_le
  have hS0 : 0 ≤ ∑ a, ‖g a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNσ : 0 ≤ (N : ℝ) * σ := mul_nonneg (Nat.cast_nonneg N) h.hσ
  have p1 : ∑ i, ∑ j, ‖g i * g j * Gm i j ^ 2‖ ≤
      ∑ i, ∑ j, 2 * (‖g i‖ * (‖g j‖ * ‖Pm i j‖ ^ 2)) +
        ∑ i, ∑ j, 2 * ρ * φ * (‖g i‖ * ‖g j‖) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_mul, norm_pow]
    have := mul_le_mul_of_nonneg_left (h.sq_le i j)
      (mul_nonneg (norm_nonneg (g i)) (norm_nonneg (g j)))
    linarith
  have p2 : ∑ i, ∑ j, 2 * (‖g i‖ * (‖g j‖ * ‖Pm i j‖ ^ 2)) ≤ 8 * T ^ 3 * ρ * (N * σ) := by
    have inner : ∀ i, ∑ j, ‖g j‖ * ‖Pm i j‖ ^ 2 ≤ 2 * T * ρ * (2 * T ^ 2) := by
      intro i
      calc ∑ j, ‖g j‖ * ‖Pm i j‖ ^ 2 ≤ ∑ j, 2 * T * ρ * ‖Pm i j‖ ^ 2 :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h.g_le j) (sq_nonneg _)
        _ = 2 * T * ρ * ∑ j, ‖Pm i j‖ ^ 2 := by rw [Finset.mul_sum]
        _ ≤ 2 * T * ρ * (2 * T ^ 2) := mul_le_mul_of_nonneg_left (h.hProw i) (by positivity)
    calc ∑ i, ∑ j, 2 * (‖g i‖ * (‖g j‖ * ‖Pm i j‖ ^ 2))
        = ∑ i, 2 * ‖g i‖ * ∑ j, ‖g j‖ * ‖Pm i j‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ i, 2 * ‖g i‖ * (2 * T * ρ * (2 * T ^ 2)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (inner i) (by positivity)
      _ = 8 * T ^ 3 * ρ * ∑ i, ‖g i‖ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 8 * T ^ 3 * ρ * (N * σ) := mul_le_mul_of_nonneg_left hS1 (by positivity)
  have p3 : ∑ i, ∑ j, 2 * ρ * φ * (‖g i‖ * ‖g j‖) ≤ 2 * ρ * φ * (N * σ) ^ 2 := by
    have e : ∑ i, ∑ j, 2 * ρ * φ * (‖g i‖ * ‖g j‖) = 2 * ρ * φ * ((∑ i, ‖g i‖) * ∑ j, ‖g j‖) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [e, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hS1 hS1 hS0 hNσ)
      (by have := h.hφ; positivity)
  linarith

/-- The `ΠΠ` cancellation for the word `g_i g_j G_{ii} G_{jj}`. -/
private lemma sumX2_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) {t : Fin N → Fin N → ℂ}
    (ht : ∀ i j, ‖t i j‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B) (hc : ThrCan N g Pm t B) :
    ‖∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j))‖ ≤
      N * σ * B + 3 * T * ρ * φ * (N * σ) ^ 2 := by
  have hS1 := h.S1_le
  have hS0 : 0 ≤ ∑ a, ‖g a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hNσ : 0 ≤ (N : ℝ) * σ := mul_nonneg (Nat.cast_nonneg N) h.hσ
  have e0 : ∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j)) =
      ∑ i, ∑ j, t i j * Pm i i * Pm j j * g i * g j +
        ∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j - Pm i i * Pm j j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have e1 : ∑ i, ∑ j, t i j * Pm i i * Pm j j * g i * g j =
      ∑ j, g j * ∑ i, t i j * Pm i i * Pm j j * g i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have e : ∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j)) =
      ∑ j, g j * ∑ i, t i j * Pm i i * Pm j j * g i +
        ∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j - Pm i i * Pm j j)) := by
    rw [e0, e1]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ j, g j * ∑ i, t i j * Pm i i * Pm j j * g i‖ ≤ N * σ * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖g j * ∑ i, t i j * Pm i i * Pm j j * g i‖ ≤ ∑ j, ‖g j‖ * B := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hc.hA j) (norm_nonneg _)
      _ = (∑ j, ‖g j‖) * B := by rw [Finset.sum_mul]
      _ ≤ N * σ * B := mul_le_mul_of_nonneg_right hS1 hB
  have h2 : ‖∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j - Pm i i * Pm j j))‖ ≤
      3 * T * ρ * φ * (N * σ) ^ 2 := by
    refine (thr_tri ht _).trans ?_
    have hc0 : 0 ≤ 3 * T * ρ * φ := by
      have := h.hT; have := h.hρ; have := h.hφ; positivity
    calc ∑ i, ∑ j, ‖g i * g j * (Gm i i * Gm j j - Pm i i * Pm j j)‖
        ≤ ∑ i, ∑ j, 3 * T * ρ * φ * (‖g i‖ * ‖g j‖) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_mul]
          have := mul_le_mul_of_nonneg_left (h.prod_sub_le i i j j)
            (mul_nonneg (norm_nonneg (g i)) (norm_nonneg (g j)))
          linarith
      _ = 3 * T * ρ * φ * ((∑ i, ‖g i‖) * ∑ j, ‖g j‖) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ ≤ 3 * T * ρ * φ * ((N * σ) * (N * σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hS1 hS1 hS0 hNσ) hc0
      _ = 3 * T * ρ * φ * (N * σ) ^ 2 := by ring
  linarith

/-- The `q = 1` sum: `|∑ᵢⱼ tᵢⱼ ã₃(i,j)|`. -/
private lemma core3 (h : ThrHyp N g pv Gm Pm T ρ φ σ) {t : Fin N → Fin N → ℂ}
    (ht : ∀ i j, ‖t i j‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B) (hc : ThrCan N g Pm t B) (a0 : ℂ) :
    ‖∑ i, ∑ j, t i j * thrA a0 g Gm i j 3‖ ≤
      2 * (4 * T ^ 2 * √(N : ℝ) * (N * σ ^ 2) + 6 * T * ρ * φ * N * (N * σ ^ 2) +
        8 * T ^ 3 * ρ * (N * σ) + 2 * ρ * φ * (N * σ) ^ 2 + N * σ * B +
        3 * T * ρ * φ * (N * σ) ^ 2) := by
  have e : ∑ i, ∑ j, t i j * thrA a0 g Gm i j 3 =
      -2 * (∑ i, ∑ j, t i j * (g j ^ 2 * (Gm i i * Gm i j)) +
        ∑ i, ∑ j, t i j * (g i * g j * (Gm i i * Gm j j)) +
        ∑ i, ∑ j, t i j * (g i * g j * Gm i j ^ 2) +
        ∑ i, ∑ j, t i j * (g i ^ 2 * (Gm i j * Gm j j))) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [thrA]; ring
  rw [e, norm_mul]
  have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [h2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine norm_add₄_le.trans ?_
  have b1 := (thr_tri ht _).trans h.sumX1_le
  have b2 := h.sumX2_le ht hB hc
  have b3 := (thr_tri ht _).trans h.sumX3_le
  have b4 := (thr_tri ht _).trans h.sumX4_le
  linarith

end ThrHyp

namespace ThrCan

variable {N : ℕ} {g : Fin N → ℂ} {Pm : Matrix (Fin N) (Fin N) ℂ} {t : Fin N → Fin N → ℂ} {B : ℝ}

private lemma sel_col (hc : ThrCan N g Pm t B) {u : ℂ → ℂ} (hu : thrSel u) (k : Fin N) :
    ‖∑ i, t i k * Pm i i * u (g i)‖ ≤ B := by
  rcases hu with hu | hu
  · simpa [hu] using hc.hB k
  · have e : ∑ i, t i k * Pm i i * u (g i) =
        starRingEnd ℂ (∑ i, starRingEnd ℂ (t i k * Pm i i) * g i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hu, map_mul, Complex.conj_conj]
    rw [e, Complex.norm_conj]
    exact hc.hB' k

private lemma sel_row (hc : ThrCan N g Pm t B) {u : ℂ → ℂ} (hu : thrSel u) (k : Fin N) :
    ‖∑ j, t k j * Pm j j * u (g j)‖ ≤ B := by
  rcases hu with hu | hu
  · simpa [hu] using hc.hC k
  · have e : ∑ j, t k j * Pm j j * u (g j) =
        starRingEnd ℂ (∑ j, starRingEnd ℂ (t k j * Pm j j) * g j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hu, map_mul, Complex.conj_conj]
    rw [e, Complex.norm_conj]
    exact hc.hC' k

end ThrCan

private lemma thrSel_mul {u : ℂ → ℂ} (hu : thrSel u) (x y : ℂ) : u (x * y) = u x * u y := by
  rcases hu with hu | hu <;> simp [hu]

private lemma thrSel_neg_two {u : ℂ → ℂ} (hu : thrSel u) (x : ℂ) : u (-2 * x) = -2 * u x := by
  rcases hu with hu | hu <;> simp [hu, map_ofNat]

private lemma thrSel_comp_conj {u : ℂ → ℂ} (hu : thrSel u) :
    thrSel (fun x => starRingEnd ℂ (u x)) := by
  rcases hu with hu | hu
  · right; intro x; simp [hu]
  · left; intro x; simp [hu]

namespace ThrHyp

variable {N : ℕ} {g pv : Fin N → ℂ} {Gm Pm : Matrix (Fin N) (Fin N) ℂ} {T ρ φ σ : ℝ}

/-- The `ΠΠ`-free half of a `q = 2` word with one leg isolated: for `Y_{ij} = c_i u(g_i) X_j`,
`|∑ᵢⱼ tᵢⱼ Y_{ij} (G_{ii} − Π_{ii})|`-type remainder bound. -/
private lemma rem2_le (h : ThrHyp N g pv Gm Pm T ρ φ σ) {t : Fin N → Fin N → ℂ}
    (ht : ∀ i j, ‖t i j‖ ≤ 1) (Y : Fin N → Fin N → ℂ) (hY : ∀ i j, ‖Y i j‖ ≤ ‖g i‖ * ‖g j‖ ^ 3)
    (D : Fin N → Fin N → ℂ) (hD : ∀ i j, ‖D i j‖ ≤ φ) :
    ‖∑ i, ∑ j, t i j * (Y i j * D i j)‖ ≤ φ * (N * σ) * (2 * T * ρ * (N * σ ^ 2)) := by
  refine (thr_tri ht _).trans ?_
  have hS1 := h.S1_le
  have hS0 : 0 ≤ ∑ a, ‖g a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC := h.cube_le
  have hC0 : 0 ≤ ∑ a, ‖g a‖ ^ 3 := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ i, ∑ j, ‖Y i j * D i j‖ ≤ ∑ i, ∑ j, φ * (‖g i‖ * ‖g j‖ ^ 3) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, mul_comm φ]
        exact mul_le_mul (hY i j) (hD i j) (norm_nonneg _) (by positivity)
    _ = φ * ((∑ i, ‖g i‖) * ∑ j, ‖g j‖ ^ 3) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ φ * ((N * σ) * (2 * T * ρ * (N * σ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hS1 hC hC0 ?_) h.hφ
        exact mul_nonneg (Nat.cast_nonneg N) h.hσ
    _ = φ * (N * σ) * (2 * T * ρ * (N * σ ^ 2)) := by ring

/-- The `q = 2` sum: `|∑ᵢⱼ tᵢⱼ ã₂(i,j) u(ã₁(i,j))|` with `u` the identity or conjugation. -/
private lemma core21 (h : ThrHyp N g pv Gm Pm T ρ φ σ) {t : Fin N → Fin N → ℂ}
    (ht : ∀ i j, ‖t i j‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B) (hc : ThrCan N g Pm t B) (a0 : ℂ)
    {u : ℂ → ℂ} (hu : thrSel u) :
    ‖∑ i, ∑ j, t i j * (thrA a0 g Gm i j 2 * u (thrA a0 g Gm i j 1))‖ ≤
      2 * (2 * (2 * T * ρ * (N * σ ^ 2) * B + φ * (N * σ) * (2 * T * ρ * (N * σ ^ 2))) +
        2 * (2 * T * ρ * (N * σ ^ 2) ^ 2)) := by
  have hun : ∀ x, ‖u x‖ = ‖x‖ := thrSel_norm hu
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have hρ0 : 0 ≤ ρ := by linarith [h.hρ]
  have hC := h.cube_le
  have hS2 := h.hS2
  have hS20 : 0 ≤ ∑ a, ‖g a‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hu1 : ∀ i j, u (thrA a0 g Gm i j 1) = -2 * (u (g i) * u (g j)) := by
    intro i j
    simp only [thrA]
    rw [mul_assoc, thrSel_neg_two hu, thrSel_mul hu]
  -- the three words
  have e : ∑ i, ∑ j, t i j * (thrA a0 g Gm i j 2 * u (thrA a0 g Gm i j 1)) =
      -2 * ((∑ j, g j ^ 2 * u (g j) * ∑ i, t i j * Pm i i * u (g i) +
          ∑ i, ∑ j, t i j * ((g j ^ 2 * u (g j) * u (g i)) * (Gm i i - Pm i i))) +
        2 * ∑ i, ∑ j, t i j * (g i * g j * Gm i j * u (g i) * u (g j)) +
        (∑ i, g i ^ 2 * u (g i) * ∑ j, t i j * Pm j j * u (g j) +
          ∑ i, ∑ j, t i j * ((g i ^ 2 * u (g i) * u (g j)) * (Gm j j - Pm j j)))) := by
    have s1 : ∑ j, g j ^ 2 * u (g j) * ∑ i, t i j * Pm i i * u (g i) =
        ∑ i, ∑ j, t i j * (g j ^ 2 * u (g j) * u (g i) * Pm i i) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have s3 : ∑ i, g i ^ 2 * u (g i) * ∑ j, t i j * Pm j j * u (g j) =
        ∑ i, ∑ j, t i j * (g i ^ 2 * u (g i) * u (g j) * Pm j j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [s1, s3, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hu1]
    simp only [thrA]
    ring
  rw [e, norm_mul]
  have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [h2]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hY1 : ∀ i j, ‖g j ^ 2 * u (g j) * u (g i)‖ ≤ ‖g i‖ * ‖g j‖ ^ 3 := by
    intro i j; rw [norm_mul, norm_mul, norm_pow, hun, hun]; nlinarith [norm_nonneg (g i)]
  have hY3 : ∀ i j, ‖g i ^ 2 * u (g i) * u (g j)‖ ≤ ‖g j‖ * ‖g i‖ ^ 3 := by
    intro i j; rw [norm_mul, norm_mul, norm_pow, hun, hun]; nlinarith [norm_nonneg (g j)]
  -- the Π-parts
  have p1 : ‖∑ j, g j ^ 2 * u (g j) * ∑ i, t i j * Pm i i * u (g i)‖ ≤
      2 * T * ρ * (N * σ ^ 2) * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖g j ^ 2 * u (g j) * ∑ i, t i j * Pm i i * u (g i)‖ ≤ ∑ j, ‖g j‖ ^ 3 * B := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_mul, norm_pow, hun, ← pow_succ]
          exact mul_le_mul_of_nonneg_left (hc.sel_col hu j) (by positivity)
      _ = (∑ j, ‖g j‖ ^ 3) * B := by rw [Finset.sum_mul]
      _ ≤ 2 * T * ρ * (N * σ ^ 2) * B := mul_le_mul_of_nonneg_right hC hB
  have p3 : ‖∑ i, g i ^ 2 * u (g i) * ∑ j, t i j * Pm j j * u (g j)‖ ≤
      2 * T * ρ * (N * σ ^ 2) * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖g i ^ 2 * u (g i) * ∑ j, t i j * Pm j j * u (g j)‖ ≤ ∑ i, ‖g i‖ ^ 3 * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, norm_mul, norm_pow, hun, ← pow_succ]
          exact mul_le_mul_of_nonneg_left (hc.sel_row hu i) (by positivity)
      _ = (∑ i, ‖g i‖ ^ 3) * B := by rw [Finset.sum_mul]
      _ ≤ 2 * T * ρ * (N * σ ^ 2) * B := mul_le_mul_of_nonneg_right hC hB
  -- the remainders
  have r1 := h.rem2_le ht (fun i j => g j ^ 2 * u (g j) * u (g i)) hY1
    (fun i _ => Gm i i - Pm i i) (fun i _ => h.hGφ i i)
  have r3 : ‖∑ i, ∑ j, t i j * ((g i ^ 2 * u (g i) * u (g j)) * (Gm j j - Pm j j))‖ ≤
      φ * (N * σ) * (2 * T * ρ * (N * σ ^ 2)) := by
    have := h.rem2_le (t := fun j i => t i j) (fun j i => ht i j)
      (fun j i => g i ^ 2 * u (g i) * u (g j)) (fun j i => hY3 i j)
      (fun j _ => Gm j j - Pm j j) (fun j _ => h.hGφ j j)
    rw [Finset.sum_comm] at this
    exact this
  -- the middle word
  have p2 : ‖∑ i, ∑ j, t i j * (g i * g j * Gm i j * u (g i) * u (g j))‖ ≤
      2 * T * ρ * (N * σ ^ 2) ^ 2 := by
    refine (thr_tri ht _).trans ?_
    calc ∑ i, ∑ j, ‖g i * g j * Gm i j * u (g i) * u (g j)‖
        ≤ ∑ i, ∑ j, 2 * T * ρ * (‖g i‖ ^ 2 * ‖g j‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          simp only [norm_mul, hun]
          have := h.G_le i j
          have h0 : 0 ≤ ‖g i‖ ^ 2 * ‖g j‖ ^ 2 := by positivity
          nlinarith
      _ = 2 * T * ρ * ((∑ i, ‖g i‖ ^ 2) * ∑ j, ‖g j‖ ^ 2) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ ≤ 2 * T * ρ * ((N * σ ^ 2) * (N * σ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hS2 hS2 hS20 ?_) (by positivity)
          exact mul_nonneg (Nat.cast_nonneg N) (sq_nonneg σ)
      _ = 2 * T * ρ * (N * σ ^ 2) ^ 2 := by ring
  have n1 := norm_add_le (∑ j, g j ^ 2 * u (g j) * ∑ i, t i j * Pm i i * u (g i))
    (∑ i, ∑ j, t i j * ((g j ^ 2 * u (g j) * u (g i)) * (Gm i i - Pm i i)))
  have n3 := norm_add_le (∑ i, g i ^ 2 * u (g i) * ∑ j, t i j * Pm j j * u (g j))
    (∑ i, ∑ j, t i j * ((g i ^ 2 * u (g i) * u (g j)) * (Gm j j - Pm j j)))
  have n2 : ‖(2 : ℂ) * ∑ i, ∑ j, t i j * (g i * g j * Gm i j * u (g i) * u (g j))‖ ≤
      2 * (2 * T * ρ * (N * σ ^ 2) ^ 2) := by
    rw [norm_mul]; simp only [Complex.norm_ofNat]; linarith
  refine norm_add₃_le.trans ?_
  linarith

/-- The `q = 3` sum: `∑ᵢⱼ |ã₁(i,j)|³ ≤ 8 (8T³ + 8φNσ² + 16φT²)²`. -/
private lemma core111 (h : ThrHyp N g pv Gm Pm T ρ φ σ) (a0 : ℂ) :
    ∑ i, ∑ j, ‖thrA a0 g Gm i j 1‖ ^ 3 ≤
      8 * (8 * T ^ 3 + 8 * φ * (N * σ ^ 2) + 16 * φ * T ^ 2) ^ 2 := by
  have hT0 : 0 ≤ T := by linarith [h.hT]
  have hφ := h.hφ
  have hcube : ∑ a, ‖g a‖ ^ 3 ≤ 8 * T ^ 3 + 8 * φ * (N * σ ^ 2) + 16 * φ * T ^ 2 := by
    have hd2 : ∑ a, ‖g a - pv a‖ ^ 2 ≤ 2 * (N * σ ^ 2) + 4 * T ^ 2 := by
      have hpt : ∀ a, ‖g a - pv a‖ ^ 2 ≤ 2 * ‖g a‖ ^ 2 + 2 * ‖pv a‖ ^ 2 := by
        intro a
        have := norm_sub_le (g a) (pv a)
        have h5 : ‖g a - pv a‖ ^ 2 ≤ (‖g a‖ + ‖pv a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
        nlinarith [sq_nonneg (‖g a‖ - ‖pv a‖)]
      calc ∑ a, ‖g a - pv a‖ ^ 2 ≤ ∑ a, (2 * ‖g a‖ ^ 2 + 2 * ‖pv a‖ ^ 2) :=
            Finset.sum_le_sum fun a _ => hpt a
        _ = 2 * ∑ a, ‖g a‖ ^ 2 + 2 * ∑ a, ‖pv a‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * (N * σ ^ 2) + 4 * T ^ 2 := by linarith [h.hS2, h.hpv2]
    have hpt : ∀ a, ‖g a‖ ^ 3 ≤ 4 * (T * ‖pv a‖ ^ 2) + 4 * (φ * ‖g a - pv a‖ ^ 2) := by
      intro a
      have h1 : ‖g a‖ ≤ ‖pv a‖ + ‖g a - pv a‖ := by
        have := norm_add_le (pv a) (g a - pv a); simpa using this
      set x := ‖pv a‖; set y := ‖g a - pv a‖
      have hx : 0 ≤ x := norm_nonneg _
      have hy : 0 ≤ y := norm_nonneg _
      have hxT : x ≤ T := h.hpv a
      have hyφ : y ≤ φ := h.hgφ a
      have h3 : ‖g a‖ ^ 3 ≤ (x + y) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h1 3
      have h4 : (x + y) ^ 3 ≤ 4 * x ^ 3 + 4 * y ^ 3 := by
        nlinarith [sq_nonneg (x - y), mul_nonneg hx hy,
          mul_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)]
      have h5 : x ^ 3 ≤ T * x ^ 2 := by
        have := mul_le_mul_of_nonneg_right hxT (sq_nonneg x); nlinarith
      have h6 : y ^ 3 ≤ φ * y ^ 2 := by
        have := mul_le_mul_of_nonneg_right hyφ (sq_nonneg y); nlinarith
      linarith
    calc ∑ a, ‖g a‖ ^ 3 ≤ ∑ a, (4 * (T * ‖pv a‖ ^ 2) + 4 * (φ * ‖g a - pv a‖ ^ 2)) :=
          Finset.sum_le_sum fun a _ => hpt a
      _ = 4 * T * ∑ a, ‖pv a‖ ^ 2 + 4 * φ * ∑ a, ‖g a - pv a‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> refine Finset.sum_congr rfl fun a _ => by ring
      _ ≤ 4 * T * (2 * T ^ 2) + 4 * φ * (2 * (N * σ ^ 2) + 4 * T ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left h.hpv2 (by positivity))
            (mul_le_mul_of_nonneg_left hd2 (by positivity))
      _ = 8 * T ^ 3 + 8 * φ * (N * σ ^ 2) + 16 * φ * T ^ 2 := by ring
  have hC0 : 0 ≤ ∑ a, ‖g a‖ ^ 3 := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ i, ∑ j, ‖thrA a0 g Gm i j 1‖ ^ 3 = ∑ i, ∑ j, 8 * (‖g i‖ ^ 3 * ‖g j‖ ^ 3) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [thrA, norm_mul, norm_neg, Complex.norm_ofNat]
        ring
    _ = 8 * (∑ i, ‖g i‖ ^ 3) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ 8 * (8 * T ^ 3 + 8 * φ * (N * σ ^ 2) + 16 * φ * T ^ 2) ^ 2 := by
        gcongr

end ThrHyp

/-! ## The exponent comparisons of the cases `q = 1, 2, 3` (§12.2) -/

section Exponents

variable {n Ψ Φ δ C₀ c₀ : ℝ}

private lemma thr_rpow_le_one (hn : 1 ≤ n) {a : ℝ} (ha : a ≤ 0) : n ^ a ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hn ha

private lemma thr_rpow_mul (hn : 1 ≤ n) (a b : ℝ) : n ^ a * n ^ b = n ^ (a + b) :=
  (Real.rpow_add (by linarith) a b).symm

private lemma thr_rpow_sq (hn : 1 ≤ n) (a : ℝ) : (n ^ a) ^ 2 = n ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring_nf

private lemma thr_rpow_cube (hn : 1 ≤ n) (a : ℝ) : (n ^ a) ^ 3 = n ^ (3 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring_nf

/-- `n^a Ψ^k ≤ n^{a + k(−1/4 − c₀)}` from `Ψ ≤ n^{−1/4−c₀}`. -/
private lemma thr_psi_pow_le (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hΨ : Ψ ≤ n ^ (-1 / 4 - c₀)) (k : ℕ)
    (a : ℝ) : n ^ a * Ψ ^ k ≤ n ^ (a + k * (-1 / 4 - c₀)) := by
  have h1 : Ψ ^ k ≤ (n ^ (-1 / 4 - c₀)) ^ k := pow_le_pow_left₀ hΨ0 hΨ k
  rw [← Real.rpow_natCast (n ^ (-1 / 4 - c₀)), ← Real.rpow_mul (by linarith)] at h1
  rw [← thr_rpow_mul hn, mul_comm (k : ℝ)]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- (e1) `σ² ≤ x`: `n^{(C₀+3/2)δ} Ψ² ≤ n^{C₀δ} Ψ`. -/
private lemma thr_e1 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hΨ : Ψ ≤ n ^ (-1 / 4 - c₀)) (hδ : 0 < δ)
    (hc : 2 * δ ≤ c₀) :
    n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2 ≤ n ^ (C₀ * δ) * Ψ := by
  have h1 : n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2 = n ^ (C₀ * δ) * Ψ * (n ^ (3 / 2 * δ) * Ψ) := by
    have : n ^ ((C₀ + 3 / 2) * δ) = n ^ (C₀ * δ) * n ^ (3 / 2 * δ) := by
      rw [thr_rpow_mul hn]; ring_nf
    rw [this]; ring
  rw [h1]
  refine mul_le_of_le_one_right (by positivity) ?_
  have := thr_psi_pow_le hn hΨ0 hΨ 1 (3 / 2 * δ)
  rw [pow_one] at this
  exact this.trans (thr_rpow_le_one hn (by push_cast; linarith))

/-- (e2) `√n ρ φ σ² ≤ y`. -/
private lemma thr_e2 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hΨ : Ψ ≤ n ^ (-1 / 4 - c₀)) (hΦ0 : 0 ≤ Φ)
    (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * (n ^ (9 / 4 * δ) * Φ) *
      (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) ≤ n ^ (-c₀ / 2) * Φ := by
  have h1 : n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * (n ^ (9 / 4 * δ) * Φ) *
      (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) =
      (n ^ (1 / 2 + 5 / 2 * δ + 9 / 4 * δ + (C₀ + 3 / 2) * δ) * Ψ ^ 2) * Φ := by
    rw [← thr_rpow_mul hn, ← thr_rpow_mul hn, ← thr_rpow_mul hn]; ring
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ hΦ0
  refine (thr_psi_pow_le hn hΨ0 hΨ 2 _).trans ?_
  refine Real.rpow_le_rpow_of_exponent_le hn ?_
  push_cast
  nlinarith

/-- (e3) `ρ σ ≤ x`. -/
private lemma thr_e3 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) :
    n ^ (5 / 2 * δ) * (n ^ ((C₀ + 3 / 2) * δ / 2) * Ψ) ≤ n ^ (C₀ * δ) * Ψ := by
  rw [← mul_assoc, thr_rpow_mul hn]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn ?_) hΨ0
  nlinarith

/-- (e4) `√n ρ σ⁴ ≤ x²`. -/
private lemma thr_e4 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hΨ : Ψ ≤ n ^ (-1 / 4 - c₀)) (hδ : 0 < δ)
    (hC₀ : 30 ≤ C₀) (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) ^ 2 ≤
      (n ^ (C₀ * δ) * Ψ) ^ 2 := by
  have h1 : n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) ^ 2 =
      (n ^ (C₀ * δ) * Ψ) ^ 2 * (n ^ (1 / 2 + 11 / 2 * δ) * Ψ ^ 2) := by
    rw [mul_pow, mul_pow, thr_rpow_sq hn, thr_rpow_sq hn]
    have : n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * n ^ (2 * ((C₀ + 3 / 2) * δ)) =
        n ^ (2 * (C₀ * δ)) * n ^ (1 / 2 + 11 / 2 * δ) := by
      rw [thr_rpow_mul hn, thr_rpow_mul hn, thr_rpow_mul hn]; ring_nf
    linear_combination (Ψ ^ 2) ^ 2 * this
  rw [h1]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine (thr_psi_pow_le hn hΨ0 hΨ 2 _).trans (thr_rpow_le_one hn ?_)
  push_cast
  nlinarith

/-- (e5) `√n ρ φ σ³ ≤ x y`. -/
private lemma thr_e5 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hΨ : Ψ ≤ n ^ (-1 / 4 - c₀)) (hΦ0 : 0 ≤ Φ)
    (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * (n ^ (9 / 4 * δ) * Φ) *
      (n ^ ((C₀ + 3 / 2) * δ / 2) * Ψ) ^ 3 ≤ (n ^ (C₀ * δ) * Ψ) * (n ^ (-c₀ / 2) * Φ) := by
  have h1 : n ^ (1 / 2 : ℝ) * n ^ (5 / 2 * δ) * (n ^ (9 / 4 * δ) * Φ) *
      (n ^ ((C₀ + 3 / 2) * δ / 2) * Ψ) ^ 3 =
      (n ^ (C₀ * δ) * Ψ) * (n ^ (-c₀ / 2) * Φ) *
        (n ^ (1 / 2 + (C₀ / 2 + 7) * δ + c₀ / 2) * Ψ ^ 2) := by
    rw [mul_pow, thr_rpow_cube hn]
    have e : ∀ a b c d e f : ℝ, n ^ a * n ^ b * (n ^ c * Φ) * (n ^ d * Ψ ^ 3) =
        n ^ e * Ψ * (n ^ f * Φ) * (n ^ (a + b + c + d - e - f) * Ψ ^ 2) := by
      intro a b c d e f
      have : n ^ (a + b + c + d - e - f) * n ^ e * n ^ f = n ^ a * n ^ b * n ^ c * n ^ d := by
        rw [thr_rpow_mul hn, thr_rpow_mul hn, thr_rpow_mul hn, thr_rpow_mul hn, thr_rpow_mul hn]
        ring_nf
      linear_combination Φ * Ψ ^ 3 * this.symm
    rw [e]
    congr 3
    ring
  rw [h1]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine (thr_psi_pow_le hn hΨ0 hΨ 2 _).trans (thr_rpow_le_one hn ?_)
  push_cast
  nlinarith

/-- (e6) `ρ² σ² ≤ x²`. -/
private lemma thr_e6 (hn : 1 ≤ n) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) :
    (n ^ (5 / 2 * δ)) ^ 2 * (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) ≤ (n ^ (C₀ * δ) * Ψ) ^ 2 := by
  rw [mul_pow, thr_rpow_sq hn, thr_rpow_sq hn, ← mul_assoc, thr_rpow_mul hn]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn ?_) (sq_nonneg _)
  nlinarith

/-- (e8) `√n φ² σ⁴ ≤ x y²`. -/
private lemma thr_e8 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) (hΨ : Ψ ≤ n ^ (-1 / 4 - c₀))
    (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    n ^ (1 / 2 : ℝ) * (n ^ (9 / 4 * δ) * Φ) ^ 2 * (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) ^ 2 ≤
      (n ^ (C₀ * δ) * Ψ) * (n ^ (-c₀ / 2) * Φ) ^ 2 := by
  have h1 : n ^ (1 / 2 : ℝ) * (n ^ (9 / 4 * δ) * Φ) ^ 2 * (n ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2) ^ 2 =
      (n ^ (C₀ * δ) * Ψ) * (n ^ (-c₀ / 2) * Φ) ^ 2 *
        (n ^ (1 / 2 + (C₀ + 15 / 2) * δ + c₀) * Ψ ^ 3) := by
    rw [mul_pow, mul_pow, mul_pow, thr_rpow_sq hn, thr_rpow_sq hn, thr_rpow_sq hn]
    have : n ^ (1 / 2 + (C₀ + 15 / 2) * δ + c₀) * n ^ (C₀ * δ) * n ^ (2 * (-c₀ / 2)) =
        n ^ (1 / 2 : ℝ) * n ^ (2 * (9 / 4 * δ)) * n ^ (2 * ((C₀ + 3 / 2) * δ)) := by
      rw [thr_rpow_mul hn, thr_rpow_mul hn, thr_rpow_mul hn, thr_rpow_mul hn]
      ring_nf
    have hP : (Ψ ^ 2) ^ 2 = Ψ * Ψ ^ 3 := by ring
    rw [hP]
    linear_combination Φ ^ 2 * Ψ * Ψ ^ 3 * this.symm
  rw [h1]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine (thr_psi_pow_le hn hΨ0 hΨ 3 _).trans (thr_rpow_le_one hn ?_)
  push_cast
  nlinarith

/-- `κ² ≤ n^{3/2} Ψ³` from `n Ψ² ≥ κ`, `0 < κ ≤ 1`. -/
private lemma thr_low_cube (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hlow : κ ≤ n * Ψ ^ 2) : κ ^ 2 ≤ n * √n * Ψ ^ 3 := by
  have hs : √n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ √n := Real.sqrt_nonneg n
  have h2 : (κ ^ 2) ^ 2 ≤ (n * √n * Ψ ^ 3) ^ 2 := by
    have e : (n * √n * Ψ ^ 3) ^ 2 = (n * Ψ ^ 2) ^ 3 := by
      rw [mul_pow, mul_pow, hs]; ring
    rw [e]
    have h3 : κ ^ 3 ≤ (n * Ψ ^ 2) ^ 3 := pow_le_pow_left₀ hκ.le hlow 3
    have h4 : κ ^ 4 ≤ κ ^ 3 := pow_le_pow_of_le_one hκ.le hκ1 (by norm_num)
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h2

/-- (e7) `κ² ≤ n^{3/2} x³`. -/
private lemma thr_e7 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hlow : κ ≤ n * Ψ ^ 2) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) :
    κ ^ 2 ≤ n * √n * (n ^ (C₀ * δ) * Ψ) ^ 3 := by
  have h5 : Ψ ^ 3 ≤ (n ^ (C₀ * δ) * Ψ) ^ 3 := by
    refine pow_le_pow_left₀ hΨ0 ?_ 3
    exact le_mul_of_one_le_left hΨ0 (Real.one_le_rpow hn (by nlinarith))
  calc κ ^ 2 ≤ n * √n * Ψ ^ 3 := thr_low_cube hn hΨ0 hκ hκ1 hlow
    _ ≤ n * √n * (n ^ (C₀ * δ) * Ψ) ^ 3 :=
        mul_le_mul_of_nonneg_left h5 (by have := Real.sqrt_nonneg n; positivity)

/-- (e9) `κ² φ² ≤ (1 + T)² n^{3/2} x³` for `Φ ≤ 1 + T`. -/
private lemma thr_e9 (hn : 1 ≤ n) (hΨ0 : 0 ≤ Ψ) {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hlow : κ ≤ n * Ψ ^ 2) (hΦ0 : 0 ≤ Φ) (hΦ1 : Φ ≤ 1 + T) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) :
    κ ^ 2 * (n ^ (9 / 4 * δ) * Φ) ^ 2 ≤ (1 + T) ^ 2 * (n * √n * (n ^ (C₀ * δ) * Ψ) ^ 3) := by
  have hs0 : 0 ≤ √n := Real.sqrt_nonneg n
  have h1 := thr_low_cube hn hΨ0 hκ hκ1 hlow
  have hΦ2 : Φ ^ 2 ≤ (1 + T) ^ 2 := pow_le_pow_left₀ hΦ0 hΦ1 2
  have hT0 : 0 ≤ 1 + T := hΦ0.trans hΦ1
  have hexp : n ^ (2 * (9 / 4 * δ)) ≤ n ^ (3 * (C₀ * δ)) :=
    Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)
  rw [mul_pow, mul_pow, thr_rpow_sq hn, thr_rpow_cube hn]
  have hp : 0 ≤ n ^ (2 * (9 / 4 * δ)) := by positivity
  calc κ ^ 2 * (n ^ (2 * (9 / 4 * δ)) * Φ ^ 2)
      ≤ (n * √n * Ψ ^ 3) * (n ^ (2 * (9 / 4 * δ)) * (1 + T) ^ 2) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left hΦ2 hp) (by positivity) (by positivity)
    _ ≤ (n * √n * Ψ ^ 3) * (n ^ (3 * (C₀ * δ)) * (1 + T) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = (1 + T) ^ 2 * (n * √n * (n ^ (3 * (C₀ * δ)) * Ψ ^ 3)) := by ring

end Exponents

/-! ## The three sums against `M X^q` -/

section Collect

variable {n s T ρ φ σ x y : ℝ}

/-- The case `q = 1`: the inequalities (e1)–(e3) give `n^{3/2} · 32T³ (x + y)`. -/
private lemma thr_Q1 (hs : s ^ 2 = n) (hs1 : 1 ≤ s) (hT : 1 ≤ T) (hρ : 0 ≤ ρ)
    (hσ : 0 ≤ σ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (e1 : σ ^ 2 ≤ x) (e2 : s * ρ * φ * σ ^ 2 ≤ y) (e3 : ρ * σ ≤ x) :
    2 * (4 * T ^ 2 * s * (n * σ ^ 2) + 6 * T * ρ * φ * n * (n * σ ^ 2) +
        8 * T ^ 3 * ρ * (n * σ) + 2 * ρ * φ * (n * σ) ^ 2 + n * σ * (4 * T ^ 3 * ρ * s) +
        3 * T * ρ * φ * (n * σ) ^ 2) ≤ n * s * (32 * T ^ 3) * (x + y) := by
  subst hs
  have hs0 : 0 ≤ s := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have hss : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs1 (by norm_num)
  have a1 : 4 * T ^ 2 * s ^ 3 * σ ^ 2 ≤ 4 * T ^ 2 * s ^ 3 * x :=
    mul_le_mul_of_nonneg_left e1 (by positivity)
  have a2 : 6 * T * s ^ 3 * (s * ρ * φ * σ ^ 2) ≤ 6 * T * s ^ 3 * y :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  have a3 : 8 * T ^ 3 * s ^ 2 * (ρ * σ) ≤ 8 * T ^ 3 * s ^ 3 * x :=
    mul_le_mul (mul_le_mul_of_nonneg_left hss (by positivity)) e3 (by positivity) (by positivity)
  have a4 : 2 * s ^ 3 * (s * ρ * φ * σ ^ 2) ≤ 2 * s ^ 3 * y :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  have a5 : 4 * T ^ 3 * s ^ 3 * (ρ * σ) ≤ 4 * T ^ 3 * s ^ 3 * x :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  have a6 : 3 * T * s ^ 3 * (s * ρ * φ * σ ^ 2) ≤ 3 * T * s ^ 3 * y :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  have hT2 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT (by norm_num)
  have hT3 : T ≤ T ^ 3 := by nlinarith
  have b1 : 4 * T ^ 2 * s ^ 3 * x ≤ 4 * T ^ 3 * s ^ 3 * x := by
    have := mul_le_mul_of_nonneg_right hT2 (by positivity : 0 ≤ 4 * s ^ 3 * x); nlinarith
  have b2 : (6 * T + 2 + 3 * T) * s ^ 3 * y ≤ 16 * T ^ 3 * s ^ 3 * y := by
    have := mul_le_mul_of_nonneg_right hT3 (by positivity : 0 ≤ s ^ 3 * y)
    nlinarith [mul_nonneg hs3 hy]
  nlinarith

/-- The case `q = 2`: the inequalities (e4)–(e6) give `n^{3/2} · 48T⁴ (x + y)²`. -/
private lemma thr_Q2 (hs : s ^ 2 = n) (hs1 : 1 ≤ s) (hT : 1 ≤ T) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (e4 : s * ρ * (σ ^ 2) ^ 2 ≤ x ^ 2) (e5 : s * ρ * φ * σ ^ 3 ≤ x * y)
    (e6 : ρ ^ 2 * σ ^ 2 ≤ x ^ 2) :
    2 * (2 * (2 * T * ρ * (n * σ ^ 2) * (4 * T ^ 3 * ρ * s) +
        φ * (n * σ) * (2 * T * ρ * (n * σ ^ 2))) + 2 * (2 * T * ρ * (n * σ ^ 2) ^ 2)) ≤
      n * s * (48 * T ^ 4) * (x + y) ^ 2 := by
  subst hs
  have hs0 : 0 ≤ s := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have a1 : 8 * T ^ 4 * s ^ 3 * (ρ ^ 2 * σ ^ 2) ≤ 8 * T ^ 4 * s ^ 3 * x ^ 2 :=
    mul_le_mul_of_nonneg_left e6 (by positivity)
  have a2 : 2 * T * s ^ 3 * (s * ρ * φ * σ ^ 3) ≤ 2 * T * s ^ 3 * (x * y) :=
    mul_le_mul_of_nonneg_left e5 (by positivity)
  have a3 : 2 * T * s ^ 3 * (s * ρ * (σ ^ 2) ^ 2) ≤ 2 * T * s ^ 3 * x ^ 2 :=
    mul_le_mul_of_nonneg_left e4 (by positivity)
  have hT4 : T ≤ T ^ 4 := by nlinarith [pow_le_pow_right₀ hT (show 1 ≤ 4 by norm_num)]
  have hxy : x ^ 2 ≤ (x + y) ^ 2 := by nlinarith
  have hxy2 : x * y ≤ (x + y) ^ 2 := by nlinarith
  have c1 : 32 * T ^ 4 * s ^ 3 * x ^ 2 ≤ 32 * T ^ 4 * s ^ 3 * (x + y) ^ 2 :=
    mul_le_mul_of_nonneg_left hxy (by positivity)
  have c2 : 8 * T * s ^ 3 * (x * y) ≤ 8 * T ^ 4 * s ^ 3 * (x + y) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hs3) hxy2 (by positivity) (by positivity)
  have c3 : 8 * T * s ^ 3 * x ^ 2 ≤ 8 * T ^ 4 * s ^ 3 * (x + y) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hs3) hxy (by positivity) (by positivity)
  nlinarith

/-- The case `q = 3`: the inequalities (e7)–(e9) give
`n^{3/2} · 9216 T⁶ (1+T)² κ⁻² (x + y)³`. -/
private lemma thr_Q3 {κ : ℝ} (hs : s ^ 2 = n) (hs1 : 1 ≤ s) (hT : 1 ≤ T)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (e7 : κ ^ 2 ≤ n * s * x ^ 3) (e8 : s * φ ^ 2 * (σ ^ 2) ^ 2 ≤ x * y ^ 2)
    (e9 : κ ^ 2 * φ ^ 2 ≤ (1 + T) ^ 2 * (n * s * x ^ 3)) :
    8 * (8 * T ^ 3 + 8 * φ * (n * σ ^ 2) + 16 * φ * T ^ 2) ^ 2 ≤
      n * s * (9216 * T ^ 6 * (1 + T) ^ 2 * (κ ^ 2)⁻¹) * (x + y) ^ 3 := by
  subst hs
  have hs0 : 0 ≤ s := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have hk2 : 0 < κ ^ 2 := by positivity
  set K := (κ ^ 2)⁻¹ with hK
  have hK1 : 1 ≤ K := one_le_inv_iff₀.2 ⟨hk2, by nlinarith⟩
  have hK0 : 0 ≤ K := by linarith
  set X := (x + y) ^ 3 with hX
  have hX0 : 0 ≤ X := by positivity
  have hx3 : x ^ 3 ≤ X := pow_le_pow_left₀ hx (by linarith) 3
  have hxy : x * y ^ 2 ≤ X := by
    rw [hX]; nlinarith [mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) hy,
      mul_nonneg (mul_nonneg hx hx) hy, pow_nonneg hx 3, pow_nonneg hy 3]
  -- 1 ≤ K s³ x³ and φ² ≤ (1+T)² K s³ x³
  have f1 : 1 ≤ K * (s ^ 3 * X) := by
    have : κ ^ 2 ≤ s ^ 3 * X := by
      have h := e7; rw [show s ^ 2 * s = s ^ 3 by ring] at h
      exact h.trans (mul_le_mul_of_nonneg_left hx3 hs3)
    calc (1 : ℝ) = K * κ ^ 2 := by rw [hK, inv_mul_cancel₀ hk2.ne']
      _ ≤ K * (s ^ 3 * X) := mul_le_mul_of_nonneg_left this hK0
  have f2 : φ ^ 2 ≤ (1 + T) ^ 2 * K * (s ^ 3 * X) := by
    have h := e9; rw [show s ^ 2 * s = s ^ 3 by ring] at h
    have h2 : κ ^ 2 * φ ^ 2 ≤ (1 + T) ^ 2 * (s ^ 3 * X) :=
      h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx3 hs3) (by positivity))
    calc φ ^ 2 = K * (κ ^ 2 * φ ^ 2) := by rw [hK, ← mul_assoc, inv_mul_cancel₀ hk2.ne', one_mul]
      _ ≤ K * ((1 + T) ^ 2 * (s ^ 3 * X)) := mul_le_mul_of_nonneg_left h2 hK0
      _ = (1 + T) ^ 2 * K * (s ^ 3 * X) := by ring
  have f3 : (φ * (s ^ 2 * σ ^ 2)) ^ 2 ≤ s ^ 3 * X := by
    have : (φ * (s ^ 2 * σ ^ 2)) ^ 2 = s ^ 3 * (s * φ ^ 2 * (σ ^ 2) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (e8.trans hxy) hs3
  set a := T ^ 3
  set b := φ * (s ^ 2 * σ ^ 2)
  set c := φ * T ^ 2
  have hsq : (8 * a + 8 * b + 16 * c) ^ 2 ≤ 3 * (64 * a ^ 2 + 64 * b ^ 2 + 256 * c ^ 2) := by
    nlinarith [sq_nonneg (8 * a - 8 * b), sq_nonneg (8 * a - 16 * c), sq_nonneg (8 * b - 16 * c)]
  have e : 8 * T ^ 3 + 8 * φ * (s ^ 2 * σ ^ 2) + 16 * φ * T ^ 2 = 8 * a + 8 * b + 16 * c := by
    simp only [a, b, c]; ring
  rw [e]
  have hT6 : 1 ≤ T ^ 6 := one_le_pow₀ hT
  have hT1 : 1 ≤ (1 + T) ^ 2 := by nlinarith
  have hP0 : 0 ≤ s ^ 3 * X := by positivity
  set P := s ^ 3 * X
  have ga : a ^ 2 ≤ T ^ 6 * (1 + T) ^ 2 * K * P := by
    have : a ^ 2 = T ^ 6 * 1 := by simp only [a]; ring
    rw [this]
    have h1 : (1 : ℝ) ≤ (1 + T) ^ 2 * (K * P) := one_le_mul_of_one_le_of_one_le hT1 f1
    calc T ^ 6 * 1 ≤ T ^ 6 * ((1 + T) ^ 2 * (K * P)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = T ^ 6 * (1 + T) ^ 2 * K * P := by ring
  have gb : b ^ 2 ≤ T ^ 6 * (1 + T) ^ 2 * K * P := by
    have h1 : (1 : ℝ) ≤ T ^ 6 * (1 + T) ^ 2 * K :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT6 hT1) hK1
    calc b ^ 2 ≤ P := f3
      _ = 1 * P := (one_mul P).symm
      _ ≤ T ^ 6 * (1 + T) ^ 2 * K * P := mul_le_mul_of_nonneg_right h1 hP0
  have gc : c ^ 2 ≤ T ^ 6 * (1 + T) ^ 2 * K * P := by
    have : c ^ 2 = T ^ 4 * φ ^ 2 := by simp only [c]; ring
    rw [this]
    have hT4 : T ^ 4 ≤ T ^ 6 := pow_le_pow_right₀ hT (by norm_num)
    calc T ^ 4 * φ ^ 2 ≤ T ^ 6 * ((1 + T) ^ 2 * K * P) :=
          mul_le_mul hT4 f2 (sq_nonneg _) (by positivity)
      _ = T ^ 6 * (1 + T) ^ 2 * K * P := by ring
  have : s ^ 2 * s * (9216 * T ^ 6 * (1 + T) ^ 2 * K) * X =
      9216 * (T ^ 6 * (1 + T) ^ 2 * K * P) := by
    simp only [P]; ring
  rw [this]
  linarith

end Collect

/-! ## The good-event bound -/

/-- On the good event: `|∑ᵢⱼ wᵢⱼ f₃(i,j)| ≤ #tuples · N^{3/2} K₀ (F^p + X^p)` with
`X = N^{C₀δ}Ψ + N^{−c₀/2}Φ`, written through the rows (e1)–(e9). -/
private lemma thr_good_bound {N : ℕ} (p : ℕ) {g pv : Fin N → ℂ}
    {Gm Pm : Matrix (Fin N) (Fin N) ℂ} {T ρ φ σ : ℝ} (h : ThrHyp N g pv Gm Pm T ρ φ σ)
    (w : Fin N → Fin N → ℂ) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (hc : ThrCan N g Pm w (4 * T ^ 3 * ρ * √(N : ℝ)))
    (hc' : ThrCan N g Pm (fun i j => starRingEnd ℂ (w i j)) (4 * T ^ 3 * ρ * √(N : ℝ)))
    (a0 : ℂ) {x y κ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hN : 1 ≤ N)
    (e1 : σ ^ 2 ≤ x) (e2 : √(N : ℝ) * ρ * φ * σ ^ 2 ≤ y) (e3 : ρ * σ ≤ x)
    (e4 : √(N : ℝ) * ρ * (σ ^ 2) ^ 2 ≤ x ^ 2) (e5 : √(N : ℝ) * ρ * φ * σ ^ 3 ≤ x * y)
    (e6 : ρ ^ 2 * σ ^ 2 ≤ x ^ 2) (e7 : κ ^ 2 ≤ N * √(N : ℝ) * x ^ 3)
    (e8 : √(N : ℝ) * φ ^ 2 * (σ ^ 2) ^ 2 ≤ x * y ^ 2)
    (e9 : κ ^ 2 * φ ^ 2 ≤ (1 + T) ^ 2 * (N * √(N : ℝ) * x ^ 3)) :
    ‖∑ i, ∑ j, w i j * fCoeff p (thrA a0 g Gm i j) 3‖ ≤
      ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) *
        (N * √(N : ℝ) * (9216 * T ^ 6 * (1 + T) ^ 2 * (κ ^ 2)⁻¹) *
          (‖a0‖ ^ p + (x + y) ^ p)) := by
  have hT := h.hT
  have hT0 : 0 ≤ T := by linarith
  have hρ0 : 0 ≤ ρ := by linarith [h.hρ]
  have hs : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs1 : 1 ≤ √(N : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  have hB : 0 ≤ 4 * T ^ 3 * ρ * √(N : ℝ) := by positivity
  set K₀ := 9216 * T ^ 6 * (1 + T) ^ 2 * (κ ^ 2)⁻¹ with hK₀
  have hk2 : 0 < κ ^ 2 := by positivity
  have hKi : 1 ≤ (κ ^ 2)⁻¹ := one_le_inv_iff₀.2 ⟨hk2, by nlinarith⟩
  have hT6 : 1 ≤ T ^ 6 := one_le_pow₀ hT
  have hT1 : 1 ≤ (1 + T) ^ 2 := by nlinarith
  have hK32 : 32 * T ^ 3 ≤ K₀ := by
    have h1 : T ^ 3 ≤ T ^ 6 := pow_le_pow_right₀ hT (by norm_num)
    have h2 : 1 ≤ (1 + T) ^ 2 * (κ ^ 2)⁻¹ := one_le_mul_of_one_le_of_one_le hT1 hKi
    have h3 : T ^ 6 * 1 ≤ T ^ 6 * ((1 + T) ^ 2 * (κ ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hK₀]; nlinarith
  have hK48 : 48 * T ^ 4 ≤ K₀ := by
    have h1 : T ^ 4 ≤ T ^ 6 := pow_le_pow_right₀ hT (by norm_num)
    have h2 : 1 ≤ (1 + T) ^ 2 * (κ ^ 2)⁻¹ := one_le_mul_of_one_le_of_one_le hT1 hKi
    have h3 : T ^ 6 * 1 ≤ T ^ 6 * ((1 + T) ^ 2 * (κ ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hK₀]; nlinarith
  have hns : 0 ≤ (N : ℝ) * √(N : ℝ) := by positivity
  have hX : 0 ≤ x + y := add_nonneg hx hy
  have hw' : ∀ i j, ‖starRingEnd ℂ (w i j)‖ ≤ 1 := fun i j => by
    rw [Complex.norm_conj]; exact hw i j
  -- the cases `q = 1, 2, 3`
  have R1 : ∀ t : Fin N → Fin N → ℂ, (∀ i j, ‖t i j‖ ≤ 1) →
      ThrCan N g Pm t (4 * T ^ 3 * ρ * √(N : ℝ)) →
      ‖∑ i, ∑ j, t i j * thrA a0 g Gm i j 3‖ ≤ N * √(N : ℝ) * K₀ * (x + y) := by
    intro t ht hct
    refine (h.core3 ht hB hct a0).trans ?_
    have := thr_Q1 hs hs1 hT hρ0 h.hσ hx hy e1 e2 e3
    have h2 : (N : ℝ) * √(N : ℝ) * (32 * T ^ 3) * (x + y) ≤ N * √(N : ℝ) * K₀ * (x + y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK32 hns) hX
    calc _ ≤ _ := le_of_eq (by ring)
      _ ≤ _ := this.trans h2
  have R2 : ∀ t : Fin N → Fin N → ℂ, (∀ i j, ‖t i j‖ ≤ 1) →
      ThrCan N g Pm t (4 * T ^ 3 * ρ * √(N : ℝ)) → ∀ u : ℂ → ℂ, thrSel u →
      ‖∑ i, ∑ j, t i j * (thrA a0 g Gm i j 2 * u (thrA a0 g Gm i j 1))‖ ≤
        N * √(N : ℝ) * K₀ * (x + y) ^ 2 := by
    intro t ht hct u hu
    refine (h.core21 ht hB hct a0 hu).trans ?_
    have := thr_Q2 hs hs1 hT hx hy e4 e5 e6
    have h2 : (N : ℝ) * √(N : ℝ) * (48 * T ^ 4) * (x + y) ^ 2 ≤
        N * √(N : ℝ) * K₀ * (x + y) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK48 hns) (sq_nonneg _)
    exact this.trans h2
  have R3 : ∑ i, ∑ j, ‖thrA a0 g Gm i j 1‖ ^ 3 ≤ N * √(N : ℝ) * K₀ * (x + y) ^ 3 :=
    (h.core111 a0).trans (thr_Q3 hs hs1 hT hx hy hκ hκ1 e7 e8 e9)
  -- the decomposition
  have hsum : ∀ (F : Fin N → Fin N → ℂ), ∑ α : Fin N × Fin N, F α.1 α.2 = ∑ i, ∑ j, F i j :=
    fun F => Fintype.sum_prod_type _
  have key := thr_fCoeff_three_le (ι := Fin N × Fin N) p
    (fun α => thrA a0 g Gm α.1 α.2) a0 (fun α => rfl) (fun α => w α.1 α.2)
    (M := N * √(N : ℝ) * K₀) (X := x + y) (by positivity) hX ?_ ?_ ?_
  · rw [← hsum (fun i j => w i j * fCoeff p (thrA a0 g Gm i j) 3)]
    exact key
  · intro f hf
    rw [hsum (fun i j => w i j * f (thrA a0 g Gm i j 3))]
    rcases hf with hf | hf
    · have e : ∑ i, ∑ j, w i j * f (thrA a0 g Gm i j 3) =
          ∑ i, ∑ j, w i j * thrA a0 g Gm i j 3 := by
        simp only [hf]
      rw [e]
      exact R1 w hw hc
    · have e : ∑ i, ∑ j, w i j * f (thrA a0 g Gm i j 3) =
          starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (w i j) * thrA a0 g Gm i j 3) := by
        simp only [map_sum, map_mul, Complex.conj_conj, hf]
      rw [e, Complex.norm_conj]
      exact R1 _ hw' hc'
  · intro f f' hf hf'
    rw [hsum (fun i j => w i j * (f (thrA a0 g Gm i j 2) * f' (thrA a0 g Gm i j 1)))]
    rcases hf with hf | hf
    · have e : ∑ i, ∑ j, w i j * (f (thrA a0 g Gm i j 2) * f' (thrA a0 g Gm i j 1)) =
          ∑ i, ∑ j, w i j * (thrA a0 g Gm i j 2 * f' (thrA a0 g Gm i j 1)) := by
        simp only [hf]
      rw [e]
      exact R2 w hw hc f' hf'
    · have e : ∑ i, ∑ j, w i j * (f (thrA a0 g Gm i j 2) * f' (thrA a0 g Gm i j 1)) =
          starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (w i j) *
            (thrA a0 g Gm i j 2 * starRingEnd ℂ (f' (thrA a0 g Gm i j 1)))) := by
        simp only [map_sum, map_mul, Complex.conj_conj, hf]
      rw [e, Complex.norm_conj]
      have R := R2 (fun i j => starRingEnd ℂ (w i j)) hw' hc' (fun z => starRingEnd ℂ (f' z))
        (thrSel_comp_conj hf')
      beta_reduce at R
      exact R
  · intro f f' f'' hf hf' hf''
    rw [hsum (fun i j => w i j * (f (thrA a0 g Gm i j 1) *
      (f' (thrA a0 g Gm i j 1) * f'' (thrA a0 g Gm i j 1))))]
    refine (thr_tri hw _).trans (le_trans ?_ R3)
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_of_eq ?_
    rw [norm_mul, norm_mul, thrSel_norm hf, thrSel_norm hf', thrSel_norm hf'']
    ring

/-! ## Measurability and the deterministic bound off the good event -/

/-- `W ↦ G^W(z)` is measurable. -/
private lemma thr_measurable_GW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z := by
  have hc : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    unfold cplx
    refine Continuous.sub ?_ continuous_const
    exact Continuous.matrix_map (continuous_id.add continuous_const) Complex.continuous_ofReal
  refine Matrix.measurable_iff.2 fun s t => ?_
  have hdet : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    (hc.matrix_det).measurable
  have hadj : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t :=
    (Matrix.measurable_iff.1 (hc.matrix_adjugate).measurable) s t
  have h : (fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t) =
      fun Wm => (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det⁻¹ *
        (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t := by
    funext Wm
    change (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ s t = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [h]
  exact hdet.inv.mul hadj

/-- `M ↦ ⟨x, M y⟩` is continuous. -/
private lemma thr_continuous_ent {N : ℕ} (x y : Fin N → ℝ) :
    Continuous fun M : Matrix (Fin N) (Fin N) ℂ => ent M x y := by
  unfold ent
  exact Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_id
    continuous_const)

/-- The order-3 coefficient of `F_v^p` is a continuous function of the resolvent matrix. -/
private lemma thr_continuous_fCoeff {N : ℕ} (p : ℕ) (P : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℝ) (i j : Fin N) :
    Continuous fun M : Matrix (Fin N) (Fin N) ℂ => fCoeff p (fun k => (-1) ^ k *
      ent (M * (deltaW i j * M) ^ k - if k = 0 then P else 0) v v) 3 := by
  have hk : ∀ k : ℕ, Continuous fun M : Matrix (Fin N) (Fin N) ℂ => (-1 : ℂ) ^ k *
      ent (M * (deltaW i j * M) ^ k - if k = 0 then P else 0) v v := by
    intro k
    refine continuous_const.mul ((thr_continuous_ent v v).comp ?_)
    fun_prop
  unfold fCoeff
  refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
  split_ifs
  · exact hk (κ r)
  · exact Complex.continuous_conj.comp (hk (κ r))

/-- The integrand `ω ↦ f₃(ω)` is measurable. -/
private lemma thr_measurable_coeff {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (W : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hW : ∀ i j, Measurable fun ω => W ω i j) (p : ℕ) (v : Fin N → ℝ) (i j : Fin N) :
    Measurable fun ω => fCoeff p (resCoeffW A (W ω) z v i j) 3 := by
  have hWm : Measurable W := Matrix.measurable_iff.2 hW
  have h := (thr_continuous_fCoeff p (piW A z) v i j).measurable.comp
    ((thr_measurable_GW A z).comp hWm)
  exact h

/-- `ω ↦ F_v(W(ω), z)` is measurable. -/
private lemma thr_measurable_Fv {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (W : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hW : ∀ i j, Measurable fun ω => W ω i j) (v : Fin N → ℝ) :
    Measurable fun ω => FvW A (W ω) z v := by
  have hWm : Measurable W := Matrix.measurable_iff.2 hW
  have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => ‖ent (M - piW A z) v v‖ :=
    continuous_norm.comp ((thr_continuous_ent v v).comp (continuous_id.sub continuous_const))
  exact hc.measurable.comp ((thr_measurable_GW A z).comp hWm)

/-- `|a_k| ≤ (2E)^{k+1}`, `k ≤ 3`, from `|G_{va}|, |G_{ab}|, |a_0| ≤ E`. -/
private lemma thr_crude_aux {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) {v : Fin N → ℝ} {i j : Fin N} {E : ℝ}
    (hE1 : 1 ≤ E) (hg : ∀ a, ‖ent (GW A Wm z) v (eI a)‖ ≤ E)
    (hGab : ∀ a b, ‖GW A Wm z a b‖ ≤ E) (ha0 : ‖ent (GW A Wm z - piW A z) v v‖ ≤ E)
    (hlam : ‖((thrLam i j : ℝ) : ℂ)‖ ≤ 1) {k : ℕ} (hk : k ≤ 3) :
    ‖resCoeffW A Wm z v i j k‖ ≤ (2 * E) ^ (k + 1) := by
  set G := GW A Wm z
  rw [thr_resCoeffW_eq hA hW hz v i j hk, norm_mul, norm_pow]
  have hlk : ‖((thrLam i j : ℝ) : ℂ)‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hlam
  have hE0 : 0 ≤ E := by linarith
  have hb : ‖thrA (ent (G - piW A z) v v) (fun a => ent G v (eI a)) G i j k‖ ≤
      (2 * E) ^ (k + 1) := by
    have hgi := hg i; have hgj := hg j
    have hn0 : ∀ a, 0 ≤ ‖ent G v (eI a)‖ := fun a => norm_nonneg _
    interval_cases k
    · simp only [thrA]; rw [show (2 * E) ^ (0 + 1) = 2 * E by ring]; linarith
    · simp only [thrA, norm_mul, norm_neg, Complex.norm_ofNat]
      rw [show (2 * E) ^ (1 + 1) = 4 * E ^ 2 by ring]
      have := mul_le_mul hgi hgj (hn0 j) hE0
      nlinarith
    · simp only [thrA]
      refine norm_add₃_le.trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
      rw [show (2 * E) ^ (2 + 1) = 8 * E ^ 3 by ring]
      have h1 : ‖ent G v (eI j)‖ ^ 2 * ‖G i i‖ ≤ E ^ 2 * E :=
        mul_le_mul (pow_le_pow_left₀ (hn0 j) hgj 2) (hGab i i) (norm_nonneg _) (by positivity)
      have h2 : ‖ent G v (eI i)‖ * ‖ent G v (eI j)‖ * ‖G i j‖ ≤ E * E * E :=
        mul_le_mul (mul_le_mul hgi hgj (hn0 j) hE0) (hGab i j) (norm_nonneg _) (by positivity)
      have h3 : ‖ent G v (eI i)‖ ^ 2 * ‖G j j‖ ≤ E ^ 2 * E :=
        mul_le_mul (pow_le_pow_left₀ (hn0 i) hgi 2) (hGab j j) (norm_nonneg _) (by positivity)
      nlinarith
    · simp only [thrA, norm_mul, norm_neg, Complex.norm_ofNat]
      have h1 : ‖ent G v (eI j) * G i i + ent G v (eI i) * G i j‖ ≤ 2 * E ^ 2 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul hgj (hGab i i) (norm_nonneg _) hE0
        have := mul_le_mul hgi (hGab i j) (norm_nonneg _) hE0
        nlinarith
      have h2 : ‖ent G v (eI j) * G i j + ent G v (eI i) * G j j‖ ≤ 2 * E ^ 2 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul hgj (hGab i j) (norm_nonneg _) hE0
        have := mul_le_mul hgi (hGab j j) (norm_nonneg _) hE0
        nlinarith
      have := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      rw [show (2 * E) ^ (3 + 1) = 16 * E ^ 4 by ring]
      nlinarith
  calc ‖((thrLam i j : ℝ) : ℂ)‖ ^ k * ‖thrA (ent (G - piW A z) v v)
        (fun a => ent G v (eI a)) G i j k‖ ≤ 1 * (2 * E) ^ (k + 1) :=
        mul_le_mul hlk hb (norm_nonneg _) zero_le_one
    _ = (2 * E) ^ (k + 1) := one_mul _

/-- The deterministic bound: `|ã_k| ≤ (2E)^{k+1}` with `E = η⁻¹ + T`, hence
`|f₃| ≤ 4^p (2E)^{p+3}`. -/
private lemma thr_crude {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) {T : ℝ} (hT : 1 ≤ T)
    (hP : ∀ x y : Fin N → ℝ, ‖testBilin x (piW A z) y‖ ≤ T * testNorm x * testNorm y)
    (p : ℕ) (v : Fin N → ℝ) (hv : testNorm v = 1) (i j : Fin N) :
    ‖fCoeff p (resCoeffW A Wm z v i j) 3‖ ≤ 4 ^ p * (2 * (z.im⁻¹ + T)) ^ (3 + p) := by
  set E := z.im⁻¹ + T with hE
  have hη : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  have hE1 : 1 ≤ E := by linarith
  set G := GW A Wm z
  have hGn : ∀ x y : Fin N → ℝ, ‖ent G x y‖ ≤ z.im⁻¹ * testNorm x * testNorm y :=
    fun x y => thr_G_norm_le hA hW hz x y
  have hg : ∀ a, ‖ent G v (eI a)‖ ≤ E := fun a => by
    have := hGn v (eI a); rw [hv, thr_testNorm_eI] at this; linarith
  have hGab : ∀ a b, ‖G a b‖ ≤ E := fun a b => by
    have := hGn (eI a) (eI b); rw [thr_testNorm_eI, thr_testNorm_eI, ent_eI_eI] at this
    linarith
  have ha0 : ‖ent (G - piW A z) v v‖ ≤ E := by
    have e : ent (G - piW A z) v v = ent G v v - ent (piW A z) v v := by
      simp [ent, sub_mulVec, dotProduct_sub]
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hGn v v; have h2 := hP v v
    rw [hv] at h1 h2
    change ‖ent (piW A z) v v‖ ≤ T * 1 * 1 at h2
    linarith
  have hlam : ‖((thrLam i j : ℝ) : ℂ)‖ ≤ 1 := by
    unfold thrLam; split_ifs <;> norm_num
  have hcoef : ∀ k ≤ 3, ‖resCoeffW A Wm z v i j k‖ ≤ (2 * E) ^ (k + 1) := by
    intro k hk
    exact thr_crude_aux hA hW hz hE1 hg hGab ha0 hlam hk
  calc ‖fCoeff p (resCoeffW A Wm z v i j) 3‖ ≤ (((3 : ℕ) : ℝ) + 1) ^ p * (2 * E) ^ (3 + p) :=
        norm_fCoeff_le p (by linarith) 3 hcoef
    _ = 4 ^ p * (2 * E) ^ (3 + p) := by norm_num


/-! ## From the good event to the deterministic hypotheses -/

private lemma thr_ent_sub {N : ℕ} (B C : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (B - C) x y = ent B x y - ent C x y := by
  simp [ent, sub_mulVec, dotProduct_sub]

/-- The bounds of `ThrHyp` hold for `G = G^W(z)` at a fixed symmetric `W` satisfying the
good-event inequalities. -/
private lemma thr_hyp_of_good {N : ℕ} (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) {T ρ φ σ : ℝ} (hT : 1 ≤ T)
    (hρ : 1 ≤ ρ) (hφ : 0 ≤ φ) (hσ : 0 ≤ σ)
    (hP : ∀ x y : Fin N → ℝ, ‖testBilin x (piW A z) y‖ ≤ T * testNorm x * testNorm y)
    (v : Fin N → ℝ) (hv : testNorm v = 1)
    (g1 : ∀ a b, ‖ent (GW A Wm z - piW A z) (eI a) (eI b)‖ ≤ ρ)
    (g2 : ∀ a b, ‖ent (GW A Wm z - piW A z) (eI a) (eI b)‖ ≤ φ)
    (g3 : ∀ a, ‖ent (GW A Wm z - piW A z) v (eI a)‖ ≤ ρ)
    (g4 : ∀ a, ‖ent (GW A Wm z - piW A z) v (eI a)‖ ≤ φ)
    (g5 : (ent (GW A Wm z) v v).im / (N * z.im) ≤ σ ^ 2) :
    ThrHyp N (fun a => ent (GW A Wm z) v (eI a)) (fun a => ent (piW A z) v (eI a))
      (GW A Wm z) (piW A z) T ρ φ σ := by
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨hrow, hcol, hpv2⟩ := thr_pi_rows (P := piW A z) hP v hv
  have hab : ∀ a b, ent (GW A Wm z - piW A z) (eI a) (eI b) = GW A Wm z a b - piW A z a b :=
    fun a b => by rw [thr_ent_sub, ent_eI_eI, ent_eI_eI]
  have hva : ∀ a, ent (GW A Wm z - piW A z) v (eI a) =
      ent (GW A Wm z) v (eI a) - ent (piW A z) v (eI a) := fun a => thr_ent_sub _ _ _ _
  refine ⟨hT, hρ, hφ, hσ, fun a b => ?_, hrow, hcol, fun a => ?_, hpv2, fun a b => ?_,
    fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩
  · have := hP (eI a) (eI b)
    rw [thr_testNorm_eI, thr_testNorm_eI, mul_one, mul_one] at this
    rwa [show testBilin (eI a) (piW A z) (eI b) = piW A z a b from ent_eI_eI _ a b] at this
  · have := hP v (eI a)
    rwa [hv, thr_testNorm_eI, mul_one, mul_one] at this
  · rw [← hab]; exact g1 a b
  · rw [← hab]; exact g2 a b
  · rw [← hva]; exact g3 a
  · rw [← hva]; exact g4 a
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [thr_ward hA hW hz v]
    have e : (ent (GW A Wm z) v v).im / z.im =
        N * ((ent (GW A Wm z) v v).im / (N * z.im)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left g5 hNr.le

/-- A cancellation bound `|∑ᵢ cᵢ G_{vi}| ≤ 4T³ρ√N` for a deterministic `c` with `|cᵢ| ≤ T²`,
from `|⟨v, (G − Π) x⟩| ≤ ρ |x|` at `x = Re c`, `x = Im c`. -/
private lemma thr_can_one {N : ℕ} {G P : Matrix (Fin N) (Fin N) ℂ} {T ρ : ℝ} (hT : 1 ≤ T)
    (hρ : 1 ≤ ρ) (v : Fin N → ℝ) (hpv : ∑ a, ‖ent P v (eI a)‖ ^ 2 ≤ 2 * T ^ 2)
    (c : Fin N → ℂ) (hc : ∀ i, ‖c i‖ ≤ T ^ 2)
    (hre : ‖ent (G - P) v (fun i => (c i).re)‖ ≤ ρ * testNorm (fun i => (c i).re))
    (him : ‖ent (G - P) v (fun i => (c i).im)‖ ≤ ρ * testNorm (fun i => (c i).im)) :
    ‖∑ i, c i * ent G v (eI i)‖ ≤ 4 * T ^ 3 * ρ * √(N : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hsN : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have e : ∑ i, c i * ent G v (eI i) = ∑ i, c i * ent P v (eI i) +
      (ent (G - P) v (fun i => (c i).re) + Complex.I * ent (G - P) v (fun i => (c i).im)) := by
    rw [← thr_sum_cplx, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [thr_ent_sub]; ring
  have hnorm : ∀ f : ℂ → ℝ, (∀ x, |f x| ≤ ‖x‖) →
      testNorm (fun i => f (c i)) ≤ T ^ 2 * √(N : ℝ) := by
    intro f hf
    unfold testNorm
    have h1 : ∑ i, f (c i) ^ 2 ≤ N * (T ^ 2) ^ 2 := by
      calc ∑ i, f (c i) ^ 2 ≤ ∑ _i : Fin N, (T ^ 2) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := (hf (c i)).trans (hc i)
            have h0 : 0 ≤ |f (c i)| := abs_nonneg _
            rw [← sq_abs]; exact pow_le_pow_left₀ h0 this 2
        _ = N * (T ^ 2) ^ 2 := by simp
    calc √(∑ i, f (c i) ^ 2) ≤ √(N * (T ^ 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = T ^ 2 * √(N : ℝ) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq (by positivity)]; ring
  have hR := hnorm Complex.re Complex.abs_re_le_norm
  have hI := hnorm Complex.im Complex.abs_im_le_norm
  have h1 : ‖∑ i, c i * ent P v (eI i)‖ ≤ 2 * T ^ 3 * √(N : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖c i * ent P v (eI i)‖ ≤ ∑ i, T ^ 2 * ‖ent P v (eI i)‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
      _ = T ^ 2 * ∑ i, ‖ent P v (eI i)‖ := by rw [Finset.mul_sum]
      _ ≤ T ^ 2 * (√(N : ℝ) * √(2 * T ^ 2)) :=
          mul_le_mul_of_nonneg_left ((thr_sum_norm_le _).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpv) hsN)) (by positivity)
      _ ≤ T ^ 2 * (√(N : ℝ) * (2 * T)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hsN) (by positivity)
          rw [Real.sqrt_le_left (by positivity)]; nlinarith
      _ = 2 * T ^ 3 * √(N : ℝ) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖ent (G - P) v (fun i => (c i).re) + Complex.I * ent (G - P) v (fun i => (c i).im)‖
      ≤ 2 * T ^ 2 * ρ * √(N : ℝ) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have := mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ ρ)
    have := mul_le_mul_of_nonneg_left hI (by linarith : (0 : ℝ) ≤ ρ)
    nlinarith
  have h3 : 2 * T ^ 3 * √(N : ℝ) + 2 * T ^ 2 * ρ * √(N : ℝ) ≤ 4 * T ^ 3 * ρ * √(N : ℝ) := by
    have hT2 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT (by norm_num)
    have a1 : 2 * T ^ 3 * √(N : ℝ) * 1 ≤ 2 * T ^ 3 * √(N : ℝ) * ρ :=
      mul_le_mul_of_nonneg_left hρ (by positivity)
    have a2 : 2 * ρ * √(N : ℝ) * T ^ 2 ≤ 2 * ρ * √(N : ℝ) * T ^ 3 :=
      mul_le_mul_of_nonneg_left hT2 (by positivity)
    nlinarith
  linarith

/-- The deterministic vectors of the cancellation bounds, for weights `t` and the index `k`. -/
private def thrVec {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (t : Fin N → Fin N → ℂ) (k : Fin N) :
    Fin 5 → Fin N → ℂ :=
  ![fun i => t i k * P i i * P k k, fun i => t i k * P i i,
    fun i => starRingEnd ℂ (t i k * P i i), fun j => t k j * P j j,
    fun j => starRingEnd ℂ (t k j * P j j)]

/-- `ThrCan` from the bounds `|⟨v, (G − Π) x⟩| ≤ ρ |x|` at the real and imaginary parts of the
vectors `thrVec`. -/
private lemma thr_can_of_good {N : ℕ} {G P : Matrix (Fin N) (Fin N) ℂ} {T ρ : ℝ} (hT : 1 ≤ T)
    (hρ : 1 ≤ ρ) (v : Fin N → ℝ) (hpv : ∑ a, ‖ent P v (eI a)‖ ^ 2 ≤ 2 * T ^ 2)
    (hP : ∀ a b, ‖P a b‖ ≤ T) {t : Fin N → Fin N → ℂ} (ht : ∀ i j, ‖t i j‖ ≤ 1)
    (hgood : ∀ k m, ‖ent (G - P) v (fun i => (thrVec P t k m i).re)‖ ≤
        ρ * testNorm (fun i => (thrVec P t k m i).re) ∧
      ‖ent (G - P) v (fun i => (thrVec P t k m i).im)‖ ≤
        ρ * testNorm (fun i => (thrVec P t k m i).im)) :
    ThrCan N (fun a => ent G v (eI a)) P t (4 * T ^ 3 * ρ * √(N : ℝ)) := by
  have hT0 : 0 ≤ T := by linarith
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hb1 : ∀ i k, ‖t i k * P i i‖ ≤ T ^ 2 := fun i k => by
    rw [norm_mul]
    calc ‖t i k‖ * ‖P i i‖ ≤ 1 * T := mul_le_mul (ht i k) (hP i i) (norm_nonneg _) zero_le_one
      _ ≤ T ^ 2 := by linarith
  have hb2 : ∀ i k, ‖t i k * P i i * P k k‖ ≤ T ^ 2 := fun i k => by
    rw [norm_mul, norm_mul, sq]
    exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) (ht i k) |>.trans (hP i i))
      (hP k k) (norm_nonneg _) hT0
  have hb3 : ∀ k j, ‖t k j * P j j‖ ≤ T ^ 2 := fun k j => by
    rw [norm_mul]
    calc ‖t k j‖ * ‖P j j‖ ≤ 1 * T := mul_le_mul (ht k j) (hP j j) (norm_nonneg _) zero_le_one
      _ ≤ T ^ 2 := by linarith
  have one : ∀ k (m : Fin 5), (∀ i, ‖thrVec P t k m i‖ ≤ T ^ 2) →
      ‖∑ i, thrVec P t k m i * ent G v (eI i)‖ ≤ 4 * T ^ 3 * ρ * √(N : ℝ) :=
    fun k m hc => thr_can_one hT hρ v hpv _ hc (hgood k m).1 (hgood k m).2
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · have := one k 0 (fun i => by simpa [thrVec] using hb2 i k)
    simpa [thrVec] using this
  · have := one k 1 (fun i => by simpa [thrVec] using hb1 i k)
    simpa [thrVec] using this
  · have := one k 2 (fun i => by simpa [thrVec, Complex.norm_conj] using hb1 i k)
    simpa [thrVec] using this
  · have := one k 3 (fun j => by simpa [thrVec] using hb3 k j)
    simpa [thrVec] using this
  · have := one k 4 (fun j => by simpa [thrVec, Complex.norm_conj] using hb3 k j)
    simpa [thrVec] using this

/-- A sum over `{(i, j) : i ≤ j}` as a double sum. -/
private lemma thr_sum_upper {N : ℕ} (f : UpperIdx N → ℂ) :
    ∑ α, f α = ∑ i, ∑ j, if h : i ≤ j then f ⟨(i, j), h⟩ else 0 := by
  set F : Fin N × Fin N → ℂ := fun q => if h : q.1 ≤ q.2 then f ⟨q, h⟩ else 0 with hF
  calc ∑ α, f α = ∑ α : UpperIdx N, F α.1 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        simp [hF, α.2]
    _ = ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => q.1 ≤ q.2), F q :=
        (Finset.sum_subtype _ (by simp) F).symm
    _ = ∑ q, F q := by
        refine Finset.sum_filter_of_ne fun q _ hq => ?_
        by_contra h
        simp [hF, h] at hq
    _ = ∑ i, ∑ j, if h : i ≤ j then f ⟨(i, j), h⟩ else 0 := Fintype.sum_prod_type _

/-! ## Assembly helpers -/

/-- A union bound over a finite index type. -/
private lemma thr_measure_iUnion_le {Ω ι : Type*} [MeasureSpace Ω] [Fintype ι]
    (B : ι → Set Ω) {c : ℝ} (h : ∀ i, ℙ (B i) ≤ ENNReal.ofReal c) :
    ℙ (⋃ i, B i) ≤ ENNReal.ofReal (Fintype.card ι * c) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc ∑ i, ℙ (B i) ≤ ∑ _i : ι, ENNReal.ofReal c := Finset.sum_le_sum fun i _ => h i
    _ = ENNReal.ofReal (Fintype.card ι * c) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]

/-- `(x + y)^p ≤ 2^p (x^p + y^p)` for `x, y ≥ 0`. -/
private lemma thr_add_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p : ℕ) :
    (x + y) ^ p ≤ 2 ^ p * (x ^ p + y ^ p) := by
  rcases le_total x y with h | h
  · calc (x + y) ^ p ≤ (2 * y) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * y ^ p := mul_pow 2 y p
      _ ≤ 2 ^ p * (x ^ p + y ^ p) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg hx p)) (by positivity)
  · calc (x + y) ^ p ≤ (2 * x) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * x ^ p := mul_pow 2 x p
      _ ≤ 2 ^ p * (x ^ p + y ^ p) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hy p)) (by positivity)

/-- The weights `w_{ij} = 1(i ≤ j) s_{ij} λ_{ij}³`. -/
private def thrW {N : ℕ} (s : UpperIdx N → ℂ) (i j : Fin N) : ℂ :=
  if h : i ≤ j then s ⟨(i, j), h⟩ * ((thrLam i j : ℝ) : ℂ) ^ 3 else 0

private lemma thrW_norm_le {N : ℕ} {s : UpperIdx N → ℂ} (hs : ∀ α, ‖s α‖ ≤ 1) (i j : Fin N) :
    ‖thrW s i j‖ ≤ 1 := by
  unfold thrW
  split_ifs with h
  · rw [norm_mul, norm_pow]
    have hl : ‖((thrLam i j : ℝ) : ℂ)‖ ≤ 1 := by unfold thrLam; split_ifs <;> norm_num
    have := pow_le_one₀ (norm_nonneg _) hl (n := 3)
    calc ‖s ⟨(i, j), h⟩‖ * ‖((thrLam i j : ℝ) : ℂ)‖ ^ 3 ≤ 1 * 1 :=
          mul_le_mul (hs _) this (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · simp

/-- The weighted sum over `{i ≤ j}` of the order-3 coefficients, rewritten with the rescaled
coefficients `ã` and the weights `w`. -/
private lemma thr_sum_conv {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (p : ℕ) (v : Fin N → ℝ) (s : UpperIdx N → ℂ) :
    ∑ α : UpperIdx N, s α * fCoeff p (resCoeffW A Wm z v α.1.1 α.1.2) 3 =
      ∑ i, ∑ j, thrW s i j * fCoeff p (thrA (ent (GW A Wm z - piW A z) v v)
        (fun a => ent (GW A Wm z) v (eI a)) (GW A Wm z) i j) 3 := by
  rw [thr_sum_upper]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold thrW
  split_ifs with h
  · simp only
    rw [thr_fCoeff_scale p 3 (thrLam i j) fun k hk => thr_resCoeffW_eq hA hW hz v i j hk]
    ring
  · simp

private lemma thr_card_upper (N : ℕ) : (Fintype.card (UpperIdx N) : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h := Fintype.card_subtype_le (fun q : Fin N × Fin N => q.1 ≤ q.2)
  rw [Fintype.card_prod, Fintype.card_fin] at h
  have : ((Fintype.card (UpperIdx N) : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h
  rw [sq]; push_cast at this; exact this

/-- The pointwise bound on the good event, for a fixed symmetric `W`. -/
private lemma thr_pointwise {N : ℕ} (hN : 1 ≤ N) (p : ℕ) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) {T : ℝ} (hT : 1 ≤ T)
    (hPi : ∀ x y : Fin N → ℝ, ‖testBilin x (piW A z) y‖ ≤ T * testNorm x * testNorm y)
    (v : Fin N → ℝ) (hv : testNorm v = 1) (s : UpperIdx N → ℂ) (hs : ∀ α, ‖s α‖ ≤ 1)
    {ρ φ σ x y κ : ℝ} (hρ : 1 ≤ ρ) (hφ : 0 ≤ φ) (hσ : 0 ≤ σ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (e1 : σ ^ 2 ≤ x) (e2 : √(N : ℝ) * ρ * φ * σ ^ 2 ≤ y) (e3 : ρ * σ ≤ x)
    (e4 : √(N : ℝ) * ρ * (σ ^ 2) ^ 2 ≤ x ^ 2) (e5 : √(N : ℝ) * ρ * φ * σ ^ 3 ≤ x * y)
    (e6 : ρ ^ 2 * σ ^ 2 ≤ x ^ 2) (e7 : κ ^ 2 ≤ N * √(N : ℝ) * x ^ 3)
    (e8 : √(N : ℝ) * φ ^ 2 * (σ ^ 2) ^ 2 ≤ x * y ^ 2)
    (e9 : κ ^ 2 * φ ^ 2 ≤ (1 + T) ^ 2 * (N * √(N : ℝ) * x ^ 3))
    (g1 : ∀ a b, ‖testBilin (eI a) (GW A Wm z - piW A z) (eI b)‖ ≤ ρ)
    (g2 : ∀ a b, ‖testBilin (eI a) (GW A Wm z - piW A z) (eI b)‖ ≤ φ)
    (g3 : ∀ a, ‖testBilin v (GW A Wm z - piW A z) (eI a)‖ ≤ ρ)
    (g4 : ∀ a, ‖testBilin v (GW A Wm z - piW A z) (eI a)‖ ≤ φ)
    (g5 : (ent (GW A Wm z) v v).im / (N * z.im) ≤ σ ^ 2)
    (g6 : ∀ (b : Bool) k m,
      ‖testBilin v (GW A Wm z - piW A z) (fun i => (thrVec (piW A z)
        (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).re)‖ ≤
        ρ * testNorm (fun i => (thrVec (piW A z)
          (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).re) ∧
      ‖testBilin v (GW A Wm z - piW A z) (fun i => (thrVec (piW A z)
        (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).im)‖ ≤
        ρ * testNorm (fun i => (thrVec (piW A z)
          (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).im)) :
    ‖∑ α : UpperIdx N, s α * fCoeff p (resCoeffW A Wm z v α.1.1 α.1.2) 3‖ ≤
      ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) *
        (N * √(N : ℝ) * (9216 * T ^ 6 * (1 + T) ^ 2 * (κ ^ 2)⁻¹) *
          (FvW A Wm z v ^ p + (x + y) ^ p)) := by
  have h := thr_hyp_of_good hN hA hW hz hT hρ hφ hσ hPi v hv g1 g2 g3 g4 g5
  have hpv2 := h.hpv2
  have hw := thrW_norm_le hs
  have hw' : ∀ i j, ‖starRingEnd ℂ (thrW s i j)‖ ≤ 1 := fun i j => by
    rw [Complex.norm_conj]; exact hw i j
  have hc := thr_can_of_good hT hρ v hpv2 h.hP hw (fun k m => by
    have h6 := g6 true k m
    simp only [↓reduceIte] at h6
    exact h6)
  have hc' := thr_can_of_good hT hρ v hpv2 h.hP hw' (fun k m => by
    have h6 := g6 false k m
    simp only [Bool.false_eq_true, ↓reduceIte] at h6
    exact h6)
  rw [thr_sum_conv hA hW hz p v s]
  exact thr_good_bound p h (thrW s) hw hc hc' _ hx hy hκ hκ1 hN e1 e2 e3 e4 e5 e6 e7 e8 e9

/-- Integration of the pointwise bounds: on the good event the sum is at most
`K (F^p + X^p)`, everywhere at most `M`. -/
private lemma thr_integrate {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {ι : Type*} [Fintype ι] (f : ι → Ω → ℂ) (s : ι → ℂ) (hf : ∀ i, Measurable (f i))
    {Mi : ℝ} (hfb : ∀ i ω, ‖f i ω‖ ≤ Mi) (F : Ω → ℝ) (hF : Measurable F) {Fb : ℝ}
    (hF0 : ∀ ω, 0 ≤ F ω) (hFb : ∀ ω, F ω ≤ Fb) (p : ℕ) (Bad : Set Ω) {M K X : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hM : ∀ ω, ‖∑ i, s i * f i ω‖ ≤ M)
    (hgood : ∀ ω, ω ∉ Bad → ‖∑ i, s i * f i ω‖ ≤ K * (F ω ^ p + X ^ p)) :
    ‖∑ i, s i * ∫ ω, f i ω‖ ≤ K * ((∫ ω, F ω ^ p) + X ^ p) + (ℙ : Measure Ω).real Bad * M := by
  have hfi : ∀ i, Integrable (f i) := fun i =>
    Integrable.of_bound (hf i).aestronglyMeasurable Mi (Filter.Eventually.of_forall (hfb i))
  have hFp : Integrable fun ω => F ω ^ p := by
    refine Integrable.of_bound (hF.pow_const p).aestronglyMeasurable (Fb ^ p)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hF0 ω) p)]
    exact pow_le_pow_left₀ (hF0 ω) (hFb ω) p
  have hsum : ∑ i, s i * ∫ ω, f i ω = ∫ ω, ∑ i, s i * f i ω := by
    rw [integral_finsetSum _ fun i _ => (hfi i).const_mul (s i)]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul (s i) (f i)).symm
  have hint : Integrable fun ω => ∑ i, s i * f i ω :=
    integrable_finsetSum _ fun i _ => (hfi i).const_mul (s i)
  set B' := toMeasurable (ℙ : Measure Ω) Bad
  have hB' : MeasurableSet B' := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, ‖∑ i, s i * f i ω‖ ≤ K * (F ω ^ p + X ^ p) + B'.indicator (fun _ => M) ω := by
    intro ω
    have hK0 : 0 ≤ K * (F ω ^ p + X ^ p) := mul_nonneg hK (by have := hF0 ω; positivity)
    by_cases hω : ω ∈ B'
    · rw [Set.indicator_of_mem hω]; linarith [hM ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact hgood ω fun h => hω (subset_toMeasurable _ _ h)
  have hbd : Integrable fun ω => K * (F ω ^ p + X ^ p) + B'.indicator (fun _ => M) ω :=
    ((hFp.add (integrable_const _)).const_mul K).add ((integrable_const M).indicator hB')
  have h1 : Integrable fun ω => K * (F ω ^ p + X ^ p) :=
    (hFp.add (integrable_const _)).const_mul K
  have h2 : Integrable fun ω => B'.indicator (fun _ => M) ω := (integrable_const M).indicator hB'
  have i1 : ∫ ω, K * (F ω ^ p + X ^ p) = K * ((∫ ω, F ω ^ p) + X ^ p) := by
    rw [integral_const_mul, integral_add hFp (integrable_const _), integral_const,
      probReal_univ, one_smul]
  have i2 : ∫ ω, B'.indicator (fun _ => M) ω = (ℙ : Measure Ω).real Bad * M := by
    rw [integral_indicator_const M hB', smul_eq_mul, measureReal_def, measureReal_def,
      measure_toMeasurable]
  calc ‖∑ i, s i * ∫ ω, f i ω‖ = ‖∫ ω, ∑ i, s i * f i ω‖ := by rw [hsum]
    _ ≤ ∫ ω, ‖∑ i, s i * f i ω‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (K * (F ω ^ p + X ^ p) + B'.indicator (fun _ => M) ω) :=
        integral_mono hint.norm (h1.add h2) hpt
    _ = K * ((∫ ω, F ω ^ p) + X ^ p) + (ℙ : Measure Ω).real Bad * M := by
        rw [integral_add h1 h2, i1, i2]

/-- The good event: off a set of probability at most `(2N² + 2N + 1 + #ι) N^{−D₁}`, the bounds
`|⟨x, (G − Π) y⟩| ≤ N^{ε} a |x||y|` (and the ones with `Φ`) hold simultaneously for the unit
vectors, for `v` and for the deterministic vectors `xv`, together with the bound on `I₅`. -/
private lemma thr_bad_event {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 1 ≤ N) {ι : Type} [Fintype ι] (Gt : Ω → Matrix (Fin N) (Fin N) ℂ)
    (I5 : Ω → ℝ) (v : Fin N → ℝ) (xv : ι → Fin N → ℝ) {ε₁ εB D₁ D₂ DB c₅ a Φ : ℝ}
    (hD₂ : D₁ ≤ D₂) (hDB : D₁ ≤ DB)
    (hr : ∀ x y : Fin N → ℝ, DomAt N ε₁ D₁ (fun ω => ‖testBilin x (Gt ω) y‖)
      (fun _ => a * testNorm x * testNorm y))
    (hr2 : DomAt N ε₁ D₂ I5 (fun _ => c₅))
    (ho : ∀ x y : Fin N → ℝ, DomAt N εB DB (fun ω => ‖testBilin x (Gt ω) y‖)
      (fun _ => a * Φ * testNorm x * testNorm y)) :
    ∃ Bad : Set Ω, (ℙ : Measure Ω).real Bad ≤
        (2 * (N : ℝ) ^ 2 + 2 * N + 1 + Fintype.card ι) * (N : ℝ) ^ (-D₁) ∧
      ∀ ω, ω ∉ Bad →
        (∀ i j, ‖testBilin (eI i) (Gt ω) (eI j)‖ ≤ (N : ℝ) ^ ε₁ * a) ∧
        (∀ i j, ‖testBilin (eI i) (Gt ω) (eI j)‖ ≤ (N : ℝ) ^ εB * (a * Φ)) ∧
        (∀ i, ‖testBilin v (Gt ω) (eI i)‖ ≤ (N : ℝ) ^ ε₁ * (a * testNorm v)) ∧
        (∀ i, ‖testBilin v (Gt ω) (eI i)‖ ≤ (N : ℝ) ^ εB * (a * Φ * testNorm v)) ∧
        I5 ω ≤ (N : ℝ) ^ ε₁ * c₅ ∧
        (∀ q, ‖testBilin v (Gt ω) (xv q)‖ ≤ (N : ℝ) ^ ε₁ * (a * testNorm v * testNorm (xv q))) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set π₀ : ℝ := (N : ℝ) ^ (-D₁) with hπ₀
  have hπ0 : 0 ≤ π₀ := by positivity
  have hπ : ∀ D : ℝ, D₁ ≤ D → ENNReal.ofReal ((N : ℝ) ^ (-D)) ≤ ENNReal.ofReal π₀ :=
    fun D hD => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hNr (neg_le_neg hD))
  let B1 : Fin N × Fin N → Set Ω := fun q =>
    {ω | (N : ℝ) ^ ε₁ * (a * testNorm (eI q.1) * testNorm (eI q.2)) <
      ‖testBilin (eI q.1) (Gt ω) (eI q.2)‖}
  let B2 : Fin N × Fin N → Set Ω := fun q =>
    {ω | (N : ℝ) ^ εB * (a * Φ * testNorm (eI q.1) * testNorm (eI q.2)) <
      ‖testBilin (eI q.1) (Gt ω) (eI q.2)‖}
  let B3 : Fin N → Set Ω := fun i =>
    {ω | (N : ℝ) ^ ε₁ * (a * testNorm v * testNorm (eI i)) < ‖testBilin v (Gt ω) (eI i)‖}
  let B4 : Fin N → Set Ω := fun i =>
    {ω | (N : ℝ) ^ εB * (a * Φ * testNorm v * testNorm (eI i)) < ‖testBilin v (Gt ω) (eI i)‖}
  let B5 : Set Ω := {ω | (N : ℝ) ^ ε₁ * c₅ < I5 ω}
  let B6 : ι → Set Ω := fun q =>
    {ω | (N : ℝ) ^ ε₁ * (a * testNorm v * testNorm (xv q)) < ‖testBilin v (Gt ω) (xv q)‖}
  have P1 : ∀ q, ℙ (B1 q) ≤ ENNReal.ofReal π₀ := fun q => hr (eI q.1) (eI q.2)
  have P2 : ∀ q, ℙ (B2 q) ≤ ENNReal.ofReal π₀ := fun q =>
    le_trans (ho (eI q.1) (eI q.2)) (hπ DB hDB)
  have P3 : ∀ i, ℙ (B3 i) ≤ ENNReal.ofReal π₀ := fun i => hr v (eI i)
  have P4 : ∀ i, ℙ (B4 i) ≤ ENNReal.ofReal π₀ := fun i => le_trans (ho v (eI i)) (hπ DB hDB)
  have P5 : ℙ B5 ≤ ENNReal.ofReal π₀ := le_trans hr2 (hπ D₂ hD₂)
  have P6 : ∀ q, ℙ (B6 q) ≤ ENNReal.ofReal π₀ := fun q => hr v (xv q)
  have hreal : ∀ (X : Set Ω), ℙ X ≤ ENNReal.ofReal π₀ → (ℙ : Measure Ω).real X ≤ π₀ :=
    fun X h => by rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hπ0 h
  have hU : ∀ {κ : Type} [Fintype κ] (B : κ → Set Ω), (∀ i, ℙ (B i) ≤ ENNReal.ofReal π₀) →
      (ℙ : Measure Ω).real (⋃ i, B i) ≤ Fintype.card κ * π₀ := fun B h => by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (thr_measure_iUnion_le B h)
  refine ⟨(⋃ q, B1 q) ∪ (⋃ q, B2 q) ∪ (⋃ i, B3 i) ∪ (⋃ i, B4 i) ∪ B5 ∪ (⋃ q, B6 q), ?_, ?_⟩
  · have u1 := hU B1 P1
    have u2 := hU B2 P2
    have u3 := hU B3 P3
    have u4 := hU B4 P4
    have u5 := hreal B5 P5
    have u6 := hU B6 P6
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at u1 u2 u3 u4
    have hu := measureReal_union_le (μ := (ℙ : Measure Ω))
    have v1 := hu ((⋃ q, B1 q) ∪ (⋃ q, B2 q) ∪ (⋃ i, B3 i) ∪ (⋃ i, B4 i) ∪ B5) (⋃ q, B6 q)
    have v2 := hu ((⋃ q, B1 q) ∪ (⋃ q, B2 q) ∪ (⋃ i, B3 i) ∪ (⋃ i, B4 i)) B5
    have v3 := hu ((⋃ q, B1 q) ∪ (⋃ q, B2 q) ∪ (⋃ i, B3 i)) (⋃ i, B4 i)
    have v4 := hu ((⋃ q, B1 q) ∪ (⋃ q, B2 q)) (⋃ i, B3 i)
    have v5 := hu (⋃ q, B1 q) (⋃ q, B2 q)
    have k3 : (N : ℝ) * N * π₀ = (N : ℝ) ^ 2 * π₀ := by ring
    have k5 : (2 * (N : ℝ) ^ 2 + 2 * N + 1 + Fintype.card ι) * π₀ =
        2 * ((N : ℝ) ^ 2 * π₀) + 2 * (N * π₀) + π₀ + Fintype.card ι * π₀ := by ring
    rw [k5]
    linarith only [u1, u2, u3, u4, u5, u6, v1, v2, v3, v4, v5, k3]
  · intro ω hω
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
    obtain ⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩ := hω
    refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_, fun i => ?_, ?_, fun q => ?_⟩
    · have h := n1 (i, j)
      simp only [B1, Set.mem_ofPred_eq, not_lt] at h
      rwa [thr_testNorm_eI, thr_testNorm_eI, mul_one, mul_one] at h
    · have h := n2 (i, j)
      simp only [B2, Set.mem_ofPred_eq, not_lt] at h
      rwa [thr_testNorm_eI, thr_testNorm_eI, mul_one, mul_one] at h
    · have h := n3 i
      simp only [B3, Set.mem_ofPred_eq, not_lt] at h
      rwa [thr_testNorm_eI, mul_one] at h
    · have h := n4 i
      simp only [B4, Set.mem_ofPred_eq, not_lt] at h
      rwa [thr_testNorm_eI, mul_one] at h
    · have h := n5
      simp only [B5, Set.mem_ofPred_eq, not_lt] at h
      exact h
    · have h := n6 q
      simp only [B6, Set.mem_ofPred_eq, not_lt] at h
      exact h

/-- The final count: the good part `cd K₀ (I + X^p)` and the bad part
`P(Ξᶜ) N² · 4^p (2(η⁻¹ + T))^{p+3} ≤ 25 · 4^p (4T)^{p+3} T^p x^p`. -/
private lemma thr_final {N : ℕ} (hN : 1 ≤ N) {T η x y I cd K₀ PB L : ℝ} {p : ℕ}
    (hT : 1 ≤ T) (hη : 0 < η) (hηN : η⁻¹ ≤ N) (hx0 : 0 ≤ x) (hxl : (T * N)⁻¹ ≤ x)
    (hy0 : 0 ≤ y) (hI0 : 0 ≤ I) (hcd0 : 0 ≤ cd) (hK₀0 : 0 ≤ K₀) (hB0 : 0 ≤ PB)
    (hPB : PB ≤ 25 * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(dPrev p - 1)))
    (hL : L ≤ cd * (N * √(N : ℝ) * K₀) * (I + (x + y) ^ p) +
      PB * ((N : ℝ) ^ 2 * (4 ^ p * (2 * (η⁻¹ + T)) ^ (3 + p)))) :
    (N : ℝ) ^ (-(3 : ℝ) / 2) * L ≤
      (cd * K₀ * 2 ^ p + 25 * 4 ^ p * (4 * T) ^ (p + 3) * T ^ p) * (x ^ p + y ^ p + I) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT0 : 0 ≤ T := by linarith
  set π₀ : ℝ := (N : ℝ) ^ (-(dPrev p - 1)) with hπ₀
  have hπ0 : 0 ≤ π₀ := by positivity
  set Kb : ℝ := 25 * 4 ^ p * (4 * T) ^ (p + 3) * T ^ p with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  set Mb : ℝ := 4 ^ p * (2 * (η⁻¹ + T)) ^ (3 + p) with hMbdef
  have hsN : √(N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hN32 : (N : ℝ) ^ (-(3 : ℝ) / 2) * (N * √(N : ℝ)) = 1 := by
    rw [hsN]
    conv_lhs => rw [show (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) =
      (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) by rw [Real.rpow_one]]
    rw [thr_rpow_mul hNr, thr_rpow_mul hNr]
    norm_num
  have hN32le : (N : ℝ) ^ (-(3 : ℝ) / 2) ≤ 1 := thr_rpow_le_one hNr (by norm_num)
  have hN32nn : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
  have hMb : Mb ≤ 4 ^ p * (4 * T) ^ (p + 3) * (N : ℝ) ^ (p + 3) := by
    have h1 : 2 * (η⁻¹ + T) ≤ 4 * T * N := by
      have a1 : (N : ℝ) ≤ T * N := le_mul_of_one_le_left hN0.le hT
      have a2 : T ≤ T * N := le_mul_of_one_le_right hT0 hNr
      linarith
    have h2 : (2 * (η⁻¹ + T)) ^ (3 + p) ≤ (4 * T * N) ^ (3 + p) :=
      pow_le_pow_left₀ (by have := inv_pos.2 hη; positivity) h1 _
    rw [hMbdef, mul_assoc, show (4 * T) ^ (p + 3) * (N : ℝ) ^ (p + 3) = (4 * T * N) ^ (3 + p) by
      rw [← mul_pow, add_comm p 3]]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hexp : (N : ℝ) ^ (p + 7) * π₀ ≤ ((N : ℝ) ^ p)⁻¹ := by
    rw [hπ₀, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity),
      thr_rpow_mul hNr]
    refine Real.rpow_le_rpow_of_exponent_le hNr ?_
    have hd : dPrev p = 100 * ((p : ℝ) + 1) ^ 2 := rfl
    rw [hd]; push_cast
    nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
  have hxp : ((N : ℝ) ^ p)⁻¹ ≤ T ^ p * x ^ p := by
    have h2 : ((T * N)⁻¹) ^ p ≤ x ^ p := pow_le_pow_left₀ (by positivity) hxl p
    rw [inv_pow, mul_pow] at h2
    have hTp : 0 < T ^ p := by positivity
    have hNp : 0 < (N : ℝ) ^ p := by positivity
    calc ((N : ℝ) ^ p)⁻¹ = T ^ p * (T ^ p * (N : ℝ) ^ p)⁻¹ := by field_simp
      _ ≤ T ^ p * x ^ p := mul_le_mul_of_nonneg_left h2 hTp.le
  have hbad : (N : ℝ) ^ (-(3 : ℝ) / 2) * (PB * ((N : ℝ) ^ 2 * Mb)) ≤ Kb * x ^ p := by
    have hMb0 : 0 ≤ Mb := by have := inv_pos.2 hη; positivity
    have c1 : (N : ℝ) ^ (-(3 : ℝ) / 2) * (PB * ((N : ℝ) ^ 2 * Mb)) ≤ PB * ((N : ℝ) ^ 2 * Mb) :=
      mul_le_of_le_one_left (by positivity) hN32le
    have c2 : PB * ((N : ℝ) ^ 2 * Mb) ≤
        (25 * (N : ℝ) ^ 2 * π₀) * ((N : ℝ) ^ 2 * (4 ^ p * (4 * T) ^ (p + 3) * (N : ℝ) ^ (p + 3))) :=
      mul_le_mul hPB (mul_le_mul_of_nonneg_left hMb (by positivity)) (by positivity)
        (by positivity)
    have c3 : (25 * (N : ℝ) ^ 2 * π₀) * ((N : ℝ) ^ 2 * (4 ^ p * (4 * T) ^ (p + 3) *
        (N : ℝ) ^ (p + 3))) = 25 * 4 ^ p * (4 * T) ^ (p + 3) * ((N : ℝ) ^ (p + 7) * π₀) := by
      ring
    have c4 : 25 * 4 ^ p * (4 * T) ^ (p + 3) * ((N : ℝ) ^ (p + 7) * π₀) ≤
        25 * 4 ^ p * (4 * T) ^ (p + 3) * (T ^ p * x ^ p) :=
      mul_le_mul_of_nonneg_left (hexp.trans hxp) (by positivity)
    have c5 : 25 * 4 ^ p * (4 * T) ^ (p + 3) * (T ^ p * x ^ p) = Kb * x ^ p := by
      rw [hKb]; ring
    linarith
  have hgoodpart : (N : ℝ) ^ (-(3 : ℝ) / 2) * (cd * (N * √(N : ℝ) * K₀) * (I + (x + y) ^ p)) ≤
      cd * K₀ * I + cd * K₀ * 2 ^ p * (x ^ p + y ^ p) := by
    have e : (N : ℝ) ^ (-(3 : ℝ) / 2) * (cd * (N * √(N : ℝ) * K₀) * (I + (x + y) ^ p)) =
        cd * K₀ * I + cd * K₀ * (x + y) ^ p := by
      calc _ = ((N : ℝ) ^ (-(3 : ℝ) / 2) * (N * √(N : ℝ))) * (cd * K₀ * (I + (x + y) ^ p)) := by
            ring
        _ = _ := by rw [hN32]; ring
    rw [e]
    have h1 := thr_add_pow_le hx0 hy0 p
    have hc : 0 ≤ cd * K₀ := mul_nonneg hcd0 hK₀0
    have := mul_le_mul_of_nonneg_left h1 hc
    linarith
  have hfin : (N : ℝ) ^ (-(3 : ℝ) / 2) * L ≤
      cd * K₀ * I + cd * K₀ * 2 ^ p * (x ^ p + y ^ p) + Kb * x ^ p := by
    have h1 := mul_le_mul_of_nonneg_left hL hN32nn
    rw [mul_add] at h1
    linarith
  refine hfin.trans ?_
  have hxp0 : 0 ≤ x ^ p := pow_nonneg hx0 p
  have hyp0 : 0 ≤ y ^ p := pow_nonneg hy0 p
  have h2p : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hc : 0 ≤ cd * K₀ := mul_nonneg hcd0 hK₀0
  have a1 : cd * K₀ * I ≤ cd * K₀ * 2 ^ p * I :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc h2p) hI0
  have a2 : 0 ≤ Kb * (y ^ p + I) := mul_nonneg hKb0 (add_nonneg hyp0 hI0)
  nlinarith [a1, a2]

/-! ## Lemma 12.7, `n = 3`, case (b) -/

/-- Lemma 12.7 for `n = 3` under (b), one step of the `Φ`-iteration ((Wig_self_improv), in the
proven form with deterministic weights `s` and the absolute value outside the sum). -/
theorem wig_coeff_three (τ c₀ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ εB DB : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hc₀ : 0 < c₀) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hδc : 2 * (C₀ + 5) * δ ≤ c₀) (hεB : εB ≤ δ / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (P : ModelClassW N) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N C P A S C₀ δ (m - 1) (δ / 4) (dPrev p) → PsiSmallW c₀ (specOf A) S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
        ∀ z ∈ levelSet N δ S m, ∀ Φ : ℝ, 0 ≤ Φ → Φ ≤ 1 + τ⁻¹ →
          (∀ v w : Fin N → ℝ, DomAt N εB DB
            (fun ω => ‖testBilin v (GW A (W ω) z - piW A z) w‖)
            (fun _ => (N : ℝ) ^ (2 * δ) * Φ * testNorm v * testNorm w)) →
          (dPrev p ≤ DB) →
        ∀ v : Fin N → ℝ, testNorm v = 1 → ∀ s : UpperIdx N → ℂ, (∀ α, ‖s α‖ ≤ 1) →
          (N : ℝ) ^ (-(3 : ℝ) / 2) *
            ‖∑ α : UpperIdx N, s α * ∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) 3‖ ≤
            K * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p
              + ((N : ℝ) ^ (-c₀ / 2) * Φ) ^ p + ∫ ω, FvW A (W ω) z v ^ p) := by
  obtain ⟨N₁, hRB⟩ := wig_rough_bound τ C C₀ δ (δ / 4) (dPrev p) hτ hτ1 hδ hC₀ hC₀δ
    (by positivity)
  set T : ℝ := τ⁻¹ with hTdef
  have hT : 1 ≤ T := one_le_inv_iff₀.2 ⟨hτ, hτ1⟩
  have hT0 : 0 ≤ T := by linarith
  set κ : ℝ := ((3 * τ⁻¹ + 1) ^ 2)⁻¹ with hκdef
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκdef]; refine inv_le_one_of_one_le₀ ?_; nlinarith
  set K₀ : ℝ := 9216 * T ^ 6 * (1 + T) ^ 2 * (κ ^ 2)⁻¹ with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set cd : ℝ := ((Finset.Nat.antidiagonalTuple p 3).card : ℝ) with hcd
  have hcd0 : 0 ≤ cd := Nat.cast_nonneg _
  set Kb : ℝ := 25 * 4 ^ p * (4 * T) ^ (p + 3) * T ^ p with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  refine ⟨cd * K₀ * 2 ^ p + Kb, by positivity, max N₁ 1, ?_⟩
  intro N hN A S P m hset hm hA hPs Ω _ _ W hW hPW z hz Φ hΦ0 hΦ1 hold hDB v hv s hs
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hrb := hRB N (le_of_max_le_left hN) A S P m hset hm hA Ω W hW hPW z hz
  obtain ⟨hzim, hzE, hzlow, hzη⟩ := hset.domain.1 hz.1
  -- Ψ
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨ0 : 0 ≤ Ψ := by rw [hΨdef]; unfold PsiW; positivity
  have hΨs : Ψ ≤ (N : ℝ) ^ (-1 / 4 - c₀) := hPs z hz.1
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i =>
    (abs_specOf_le_norm hset.symmA i).trans hset.normA
  have hmim : κ * z.im ≤ (mW (specOf A) z).im := im_mW_ge hN1 hτ ha hzim hzE hzη
  have hlow : κ ≤ N * Ψ ^ 2 := by
    have h1 : √((mW (specOf A) z).im / (N * z.im)) ≤ Ψ := by
      rw [hΨdef]; unfold PsiW
      exact le_add_of_nonneg_right (by positivity)
    have h2 : (mW (specOf A) z).im / (N * z.im) ≤ Ψ ^ 2 := by
      have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      have hm0 : 0 ≤ (mW (specOf A) z).im := le_trans (by positivity) hmim
      rwa [Real.sq_sqrt (div_nonneg hm0 (by positivity))] at h3
    have h4 : κ ≤ (mW (specOf A) z).im / z.im := by
      rw [le_div_iff₀ hzim]; exact hmim
    calc κ ≤ (mW (specOf A) z).im / z.im := h4
      _ = N * ((mW (specOf A) z).im / (N * z.im)) := by field_simp
      _ ≤ N * Ψ ^ 2 := mul_le_mul_of_nonneg_left h2 hN0.le
  have hΨTN : (T * N)⁻¹ ≤ Ψ := by
    have h1 : 1 / (N * z.im) ≤ Ψ := by
      rw [hΨdef]; unfold PsiW; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    refine le_trans ?_ h1
    rw [one_div]
    refine inv_anti₀ (by positivity) ?_
    rw [mul_comm T]; exact mul_le_mul_of_nonneg_left hzη hN0.le
  -- Π
  have hPi : ∀ x y : Fin N → ℝ, ‖testBilin x (piW A z) y‖ ≤ T * testNorm x * testNorm y :=
    fun x y => norm_piW_le hτ hset.symmA hset.standing hz.1 x y
  have hpv2 : ∑ a, ‖ent (piW A z) v (eI a)‖ ^ 2 ≤ 2 * T ^ 2 := (thr_pi_rows hPi v hv).2.2
  have hPab : ∀ a b, ‖piW A z a b‖ ≤ T := fun a b => by
    have := hPi (eI a) (eI b)
    rw [thr_testNorm_eI, thr_testNorm_eI, mul_one, mul_one] at this
    rwa [show testBilin (eI a) (piW A z) (eI b) = piW A z a b from ent_eI_eI _ a b] at this
  -- the losses and the target factors
  set ρ : ℝ := (N : ℝ) ^ (5 / 2 * δ) with hρdef
  set φ : ℝ := (N : ℝ) ^ (9 / 4 * δ) * Φ with hφdef
  set σ : ℝ := (N : ℝ) ^ ((C₀ + 3 / 2) * δ / 2) * Ψ with hσdef
  set x : ℝ := (N : ℝ) ^ (C₀ * δ) * Ψ with hxdef
  set y : ℝ := (N : ℝ) ^ (-c₀ / 2) * Φ with hydef
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hNr (by positivity)
  have hφ0 : 0 ≤ φ := by positivity
  have hσ0 : 0 ≤ σ := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hσ2 : σ ^ 2 = (N : ℝ) ^ ((C₀ + 3 / 2) * δ) * Ψ ^ 2 := by
    rw [hσdef, mul_pow, thr_rpow_sq hNr]; ring_nf
  have hsq : √(N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hρeq : (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) = ρ := by
    rw [thr_rpow_mul hNr, hρdef]; ring_nf
  have hφle : ∀ c : ℝ, 0 ≤ c → (N : ℝ) ^ εB * ((N : ℝ) ^ (2 * δ) * Φ * c) ≤ φ * c := by
    intro c hc
    have h1 : (N : ℝ) ^ εB ≤ (N : ℝ) ^ (δ / 4) := Real.rpow_le_rpow_of_exponent_le hNr hεB
    have h2 : (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (2 * δ) = (N : ℝ) ^ (9 / 4 * δ) := by
      rw [thr_rpow_mul hNr]; ring_nf
    calc (N : ℝ) ^ εB * ((N : ℝ) ^ (2 * δ) * Φ * c)
        ≤ (N : ℝ) ^ (δ / 4) * ((N : ℝ) ^ (2 * δ) * Φ * c) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = φ * c := by rw [hφdef, ← h2]; ring
  have hσeq : (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ ((C₀ + 1) * δ) * Ψ ^ 2) = σ ^ 2 := by
    rw [hσ2, ← mul_assoc, thr_rpow_mul hNr]; ring_nf
  -- the inequalities (e1)–(e9)
  have hc2 : 2 * δ ≤ c₀ := by nlinarith
  have e1 : σ ^ 2 ≤ x := by rw [hσ2]; exact thr_e1 hNr hΨ0 hΨs hδ hc2
  have e2 : √(N : ℝ) * ρ * φ * σ ^ 2 ≤ y := by
    rw [hσ2, hsq]; exact thr_e2 hNr hΨ0 hΨs hΦ0 hδ hC₀ hδc
  have e3 : ρ * σ ≤ x := thr_e3 hNr hΨ0 hδ hC₀
  have e4 : √(N : ℝ) * ρ * (σ ^ 2) ^ 2 ≤ x ^ 2 := by
    rw [hσ2, hsq]; exact thr_e4 hNr hΨ0 hΨs hδ hC₀ hδc
  have e5 : √(N : ℝ) * ρ * φ * σ ^ 3 ≤ x * y := by
    rw [hsq]; exact thr_e5 hNr hΨ0 hΨs hΦ0 hδ hC₀ hδc
  have e6 : ρ ^ 2 * σ ^ 2 ≤ x ^ 2 := by rw [hσ2]; exact thr_e6 hNr hδ hC₀
  have e7 : κ ^ 2 ≤ N * √(N : ℝ) * x ^ 3 := thr_e7 hNr hΨ0 hκ0 hκ1 hlow hδ hC₀
  have e8 : √(N : ℝ) * φ ^ 2 * (σ ^ 2) ^ 2 ≤ x * y ^ 2 := by
    rw [hσ2, hsq]
    have := thr_e8 hNr hΨ0 hΨs (Φ := Φ) hδ hC₀ hδc
    linarith
  have e9 : κ ^ 2 * φ ^ 2 ≤ (1 + T) ^ 2 * (N * √(N : ℝ) * x ^ 3) :=
    thr_e9 hNr hΨ0 hκ0 hκ1 hlow hΦ0 hΦ1 hδ hC₀
  -- the good event
  have hDP : dPrev p - 1 ≤ dPrev p := sub_le_self _ zero_le_one
  have hDB' : dPrev p - 1 ≤ DB := hDP.trans hDB
  obtain ⟨Bad, hPBad0, hraw⟩ := thr_bad_event hN1 (fun ω => GW A (W ω) z - piW A z)
    (fun ω => (ent (GW A (W ω) z) v v).im / (N * z.im)) v
    (fun q : Fin N × Bool × Fin 5 × Bool => if q.2.2.2 then
      (fun i => (thrVec (piW A z) (if q.2.1 then thrW s else
        fun i j => starRingEnd ℂ (thrW s i j)) q.1 q.2.2.1 i).re)
      else (fun i => (thrVec (piW A z) (if q.2.1 then thrW s else
        fun i j => starRingEnd ℂ (thrW s i j)) q.1 q.2.2.1 i).im))
    hDP hDB' hrb.1 (hrb.2 v hv) hold
  set π₀ : ℝ := (N : ℝ) ^ (-(dPrev p - 1)) with hπ₀
  have hπ0 : 0 ≤ π₀ := by positivity
  have hPBad : (ℙ : Measure Ω).real Bad ≤ 25 * (N : ℝ) ^ 2 * π₀ := by
    refine hPBad0.trans ?_
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
      Nat.cast_ofNat]
    have k1 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
    have k2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
    have : 2 * (N : ℝ) ^ 2 + 2 * N + 1 + N * (2 * (5 * 2)) ≤ 25 * (N : ℝ) ^ 2 := by
      linarith only [k1, k2]
    exact mul_le_mul_of_nonneg_right this hπ0
  -- the bound on the good event
  have hgood : ∀ ω, ω ∉ Bad →
      ‖∑ α : UpperIdx N, s α * fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) 3‖ ≤
        cd * (N * √(N : ℝ) * K₀) * (FvW A (W ω) z v ^ p + (x + y) ^ p) := by
    intro ω hω
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hraw ω hω
    have g1 : ∀ a b, ‖testBilin (eI a) (GW A (W ω) z - piW A z) (eI b)‖ ≤ ρ := fun a b => by
      rw [← hρeq]; exact r1 a b
    have hφ1 := hφle 1 zero_le_one
    rw [mul_one, mul_one φ] at hφ1
    have g2 : ∀ a b, ‖testBilin (eI a) (GW A (W ω) z - piW A z) (eI b)‖ ≤ φ := fun a b =>
      (r2 a b).trans hφ1
    have g3 : ∀ a, ‖testBilin v (GW A (W ω) z - piW A z) (eI a)‖ ≤ ρ := fun a => by
      have h := r3 a; rwa [hv, mul_one, hρeq] at h
    have g4 : ∀ a, ‖testBilin v (GW A (W ω) z - piW A z) (eI a)‖ ≤ φ := fun a => by
      have h := r4 a; rw [hv, mul_one] at h; exact h.trans hφ1
    have g5 : (ent (GW A (W ω) z) v v).im / (N * z.im) ≤ σ ^ 2 := by
      have h := r5; rwa [hσeq] at h
    have g6 : ∀ (b : Bool) k m,
        ‖testBilin v (GW A (W ω) z - piW A z) (fun i => (thrVec (piW A z)
          (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).re)‖ ≤
          ρ * testNorm (fun i => (thrVec (piW A z)
            (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).re) ∧
        ‖testBilin v (GW A (W ω) z - piW A z) (fun i => (thrVec (piW A z)
          (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).im)‖ ≤
          ρ * testNorm (fun i => (thrVec (piW A z)
            (if b then thrW s else fun i j => starRingEnd ℂ (thrW s i j)) k m i).im) := by
      intro b k m
      have hre := r6 (k, b, m, true)
      have him := r6 (k, b, m, false)
      simp only [↓reduceIte, Bool.false_eq_true] at hre him
      rw [hv, mul_one, ← mul_assoc, hρeq] at hre him
      exact ⟨hre, him⟩
    have := thr_pointwise hN1 p hset.symmA (hW.symm ω) hzim hT hPi v hv s hs hρ1 hφ0 hσ0 hx0
      hy0 hκ0 hκ1 e1 e2 e3 e4 e5 e6 e7 e8 e9 g1 g2 g3 g4 g5 g6
    calc _ ≤ _ := this
      _ = _ := by rw [hK₀]; ring
  -- the bounds everywhere
  set Mb : ℝ := 4 ^ p * (2 * (z.im⁻¹ + T)) ^ (3 + p) with hMb
  have hcr : ∀ (α : UpperIdx N) ω,
      ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) 3‖ ≤ Mb := fun α ω =>
    thr_crude hset.symmA (hW.symm ω) hzim hT hPi p v hv α.1.1 α.1.2
  have hMb0 : 0 ≤ Mb := by positivity
  have hM : ∀ ω, ‖∑ α : UpperIdx N, s α * fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) 3‖ ≤
      (N : ℝ) ^ 2 * Mb := by
    intro ω
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : UpperIdx N, ‖s α * fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) 3‖
        ≤ ∑ _α : UpperIdx N, Mb := Finset.sum_le_sum fun α _ => by
          rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hs α) |>.trans (hcr α ω)
      _ = (Fintype.card (UpperIdx N) : ℝ) * Mb := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ 2 * Mb := mul_le_mul_of_nonneg_right (thr_card_upper N) hMb0
  have hF0 : ∀ ω, 0 ≤ FvW A (W ω) z v := fun ω => norm_nonneg _
  have hFb : ∀ ω, FvW A (W ω) z v ≤ z.im⁻¹ + T := by
    intro ω
    unfold FvW
    rw [thr_ent_sub]
    refine (norm_sub_le _ _).trans ?_
    have h1 := thr_G_norm_le hset.symmA (hW.symm ω) hzim v v
    have h2 := hPi v v
    rw [hv] at h1 h2
    change ‖ent (piW A z) v v‖ ≤ T * 1 * 1 at h2
    linarith only [h1, h2]
  have hint := thr_integrate (fun (α : UpperIdx N) ω =>
      fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) 3) s
    (fun α => thr_measurable_coeff A z W hW.measurable p v α.1.1 α.1.2) hcr
    (fun ω => FvW A (W ω) z v) (thr_measurable_Fv A z W hW.measurable v) hF0 hFb p Bad
    (K := cd * (N * √(N : ℝ) * K₀)) (X := x + y)
    (mul_nonneg hcd0 (mul_nonneg (mul_nonneg hN0.le (Real.sqrt_nonneg _)) hK₀0))
    (add_nonneg hx0 hy0) hM hgood
  have hηN' : z.im⁻¹ ≤ N := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hNr (by linarith only [hτ])
    rw [Real.rpow_neg_one] at h1
    have h2 : (N : ℝ)⁻¹ ≤ z.im := h1.trans hzlow
    calc z.im⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) h2
      _ = N := inv_inv _
  exact thr_final hN1 hT hzim hηN' hx0 (hΨTN.trans (le_mul_of_one_le_left hΨ0
    (Real.one_le_rpow hNr (by positivity)))) hy0
    (integral_nonneg fun ω => pow_nonneg (hF0 ω) p) hcd0 hK₀0 measureReal_nonneg hPBad hint

#print axioms Anisotropic.wig_coeff_three

end Anisotropic
