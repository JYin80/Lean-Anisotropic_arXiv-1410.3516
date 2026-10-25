import Anisotropic.Comparison.Ladder
import Anisotropic.Comparison.Props
import Anisotropic.Comparison.WordBounds
import Anisotropic.Comparison.Words
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
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

/-! # Lemma 12.7: the coefficients of order `n ≥ 4` -/

/-! ## The spectral form of `G^W` and the Ward identity -/

/-- A real symmetric `M` is `U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma highOrder_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
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
private lemma highOrder_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ}
    {w : ℂ} (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hMU : M = U * diagonal l * Uᵀ)
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

/-- A real matrix `Q` with `Qᵀ Q = 1` preserves `∑ₛ xₛ²`. -/
private lemma highOrder_sumsq_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (x : Fin N → ℝ) : ∑ s, (Q *ᵥ x) s ^ 2 = ∑ s, x s ^ 2 := by
  have h : (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- The sandwich `⟨v, U D Uᵀ w⟩ = ∑ₖ dₖ (Uᵀ v)ₖ (Uᵀ w)ₖ`. -/
private lemma highOrder_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
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

/-- The spectral form of `G^W(z)` for real symmetric `W + A` and `Im z > 0`: a real orthogonal
`U` and eigenvalues `λ` with `G_{xy} = ∑ₖ (λₖ − z)⁻¹ (Uᵀx)ₖ (Uᵀy)ₖ`. -/
private lemma highOrder_spectral {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) : ∃ (U : Matrix (Fin N) (Fin N) ℝ) (l : Fin N → ℝ),
      U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ (∀ k, (l k : ℂ) - z ≠ 0) ∧
      ∀ x y : Fin N → ℝ, ent (GW A Wm z) x y =
        ∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ x) k * (Uᵀ *ᵥ y) k : ℝ) : ℂ) := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := highOrder_eig_decomp (hW'.add hA)
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  refine ⟨U, l, hUU, hUU', hne, fun x y => ?_⟩
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    highOrder_resolvent_eq hUU hUU' hMU hne
  rw [hG, highOrder_ent_sandwich]

/-- `Im (λ − z)⁻¹ = Im z · |(λ − z)⁻¹|²` for real `λ`. -/
private lemma highOrder_im_inv (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).im = z.im * ‖((x : ℂ) - z)⁻¹‖ ^ 2 := by
  rw [Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  ring

/-- `|(λ − z)⁻¹| ≤ (Im z)⁻¹` for real `λ` and `Im z > 0`. -/
private lemma highOrder_norm_inv_le (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ hz ?_
  have h := Complex.abs_im_le_norm ((x : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  rwa [abs_of_pos hz] at h

/-- `G^W` is symmetric: `G_{xy} = G_{yx}`. -/
private lemma highOrder_ent_symm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x y : Fin N → ℝ) :
    ent (GW A Wm z) x y = ent (GW A Wm z) y x := by
  obtain ⟨U, l, -, -, -, hG⟩ := highOrder_spectral hA hW hz
  rw [hG, hG]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm ((Uᵀ *ᵥ x) k)]

/-- The Ward identity `∑ₛ |G_{xs}|² = Im G_{xx} / Im z`. -/
private lemma highOrder_ward {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x : Fin N → ℝ) :
    ∑ s, ‖ent (GW A Wm z) x (eI s)‖ ^ 2 = (ent (GW A Wm z) x x).im / z.im := by
  obtain ⟨U, l, hUU, hUU', hne, hG⟩ := highOrder_spectral hA hW hz
  have hUe : ∀ s k, (Uᵀ *ᵥ eI s) k = U s k := by
    intro s k
    simp [mulVec, dotProduct, eI, Pi.single_apply, transpose_apply]
  set fr : Fin N → ℝ := fun k => (((l k : ℂ) - z)⁻¹).re * (Uᵀ *ᵥ x) k with hfr
  set fi : Fin N → ℝ := fun k => (((l k : ℂ) - z)⁻¹).im * (Uᵀ *ᵥ x) k with hfi
  have hent : ∀ s, ent (GW A Wm z) x (eI s) =
      ((U *ᵥ fr) s : ℂ) + ((U *ᵥ fi) s : ℂ) * Complex.I := by
    intro s
    rw [hG]
    simp only [hUe]
    rw [show (U *ᵥ fr) s = ∑ k, U s k * fr k from rfl,
      show (U *ᵥ fi) s = ∑ k, U s k * fi k from rfl]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hck : ((l k : ℂ) - z)⁻¹ =
        ((((l k : ℂ) - z)⁻¹).re : ℂ) + ((((l k : ℂ) - z)⁻¹).im : ℂ) * Complex.I :=
      (Complex.re_add_im _).symm
    simp only [hfr, hfi]
    push_cast
    conv_lhs => rw [hck]
    ring
  have hnorm : ∀ s, ‖ent (GW A Wm z) x (eI s)‖ ^ 2 = (U *ᵥ fr) s ^ 2 + (U *ᵥ fi) s ^ 2 := by
    intro s
    rw [hent, Complex.sq_norm, Complex.normSq_add_mul_I]
  simp_rw [hnorm]
  rw [Finset.sum_add_distrib, highOrder_sumsq_orth hUU', highOrder_sumsq_orth hUU',
    ← Finset.sum_add_distrib]
  rw [hG, Complex.im_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.im_mul_ofReal, highOrder_im_inv]
  have hnk : ‖((l k : ℂ) - z)⁻¹‖ ^ 2 = (((l k : ℂ) - z)⁻¹).re ^ 2 + (((l k : ℂ) - z)⁻¹).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hnk]
  simp only [hfr, hfi]
  field_simp

/-- `|G_{xy}| ≤ (Im z)⁻¹ |x| |y|`. -/
private lemma highOrder_norm_ent_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x y : Fin N → ℝ) :
    ‖ent (GW A Wm z) x y‖ ≤ z.im⁻¹ * testNorm x * testNorm y := by
  obtain ⟨U, l, hUU, -, -, hG⟩ := highOrder_spectral hA hW hz
  have hQ : Uᵀᵀ * Uᵀ = 1 := by rw [transpose_transpose]; exact hUU
  have hx : testNorm x = √(∑ k, (Uᵀ *ᵥ x) k ^ 2) := by
    rw [highOrder_sumsq_orth hQ]; rfl
  have hy : testNorm y = √(∑ k, (Uᵀ *ᵥ y) k ^ 2) := by
    rw [highOrder_sumsq_orth hQ]; rfl
  rw [hG, hx, hy]
  have hηi : 0 ≤ z.im⁻¹ := (inv_pos.2 hz).le
  calc ‖∑ k, ((l k : ℂ) - z)⁻¹ * (((Uᵀ *ᵥ x) k * (Uᵀ *ᵥ y) k : ℝ) : ℂ)‖
      ≤ ∑ k, z.im⁻¹ * (|(Uᵀ *ᵥ x) k| * |(Uᵀ *ᵥ y) k|) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (highOrder_norm_inv_le _ hz) (by positivity)
    _ = z.im⁻¹ * ∑ k, |(Uᵀ *ᵥ x) k| * |(Uᵀ *ᵥ y) k| := by rw [Finset.mul_sum]
    _ ≤ z.im⁻¹ * (√(∑ k, |(Uᵀ *ᵥ x) k| ^ 2) * √(∑ k, |(Uᵀ *ᵥ y) k| ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hηi
    _ = _ := by simp only [sq_abs]; ring

/-! ## Products along the symmetric update direction -/

/-- `x^T B e_c = ∑ₛ xₛ B_{sc}`. -/
private lemma highOrder_ent_eI_right {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℝ)
    (c : Fin N) : ent B x (eI c) = ∑ s, (x s : ℂ) * B s c := by
  simp [ent, cvec, dotProduct, mulVec, eI, Pi.single_apply, apply_ite]

/-- `e_c^T B y = ∑ₜ B_{ct} yₜ`. -/
private lemma highOrder_ent_eI_left {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℝ)
    (c : Fin N) : ent B (eI c) y = ∑ t, B c t * (y t : ℂ) := by
  simp [ent, cvec, dotProduct, mulVec, eI, Pi.single_apply, apply_ite, ite_mul,
    Finset.sum_ite_eq']

/-- `(PQ)_{xy} = ∑_c P_{x c} Q_{c y}`. -/
private lemma highOrder_ent_mul {N : ℕ} (P Q : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (P * Q) x y = ∑ c, ent P x (eI c) * ent Q (eI c) y := by
  simp only [highOrder_ent_eI_right, highOrder_ent_eI_left, Finset.sum_mul_sum]
  simp only [ent, cvec, dotProduct, mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- A double sum against the update direction: `|∑_{c,d} f_{cd} Δ_{cd}| ≤ |f_{ij}| + |f_{ji}|`. -/
private lemma highOrder_norm_sum_delta {N : ℕ} (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    ‖∑ c, ∑ d, f c d * deltaW i j c d‖ ≤ ‖f i j‖ + ‖f j i‖ := by
  by_cases hij : i = j
  · subst hij
    have h : ∑ c, ∑ d, f c d * deltaW i i c d = f i i := by
      simp [deltaW, ite_and, Finset.sum_ite_eq']
    rw [h]
    linarith [norm_nonneg (f i i)]
  · have hd : ∀ c d, deltaW i j c d =
        (if c = i ∧ d = j then 1 else 0) + (if c = j ∧ d = i then 1 else 0) := by
      intro c d
      unfold deltaW
      by_cases h1 : c = i ∧ d = j
      · obtain ⟨rfl, rfl⟩ := h1
        simp [hij, Ne.symm hij]
      · by_cases h2 : c = j ∧ d = i
        · obtain ⟨rfl, rfl⟩ := h2
          simp [hij, Ne.symm hij]
        · simp [h1, h2]
    have h : ∑ c, ∑ d, f c d * deltaW i j c d = f i j + f j i := by
      simp only [hd, mul_add, Finset.sum_add_distrib]
      simp [ite_and, Finset.sum_ite_eq']
    rw [h]
    exact norm_add_le _ _

/-- `|(P Δ G)_{xy}| ≤ |P_{x i}| |G_{j y}| + |P_{x j}| |G_{i y}|` for the update direction
`Δ = E_{ij} + E_{ji}`. -/
private lemma highOrder_norm_ent_delta {N : ℕ} (P G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (x y : Fin N → ℝ) :
    ‖ent (P * (deltaW i j * G)) x y‖ ≤
      ‖ent P x (eI i)‖ * ‖ent G (eI j) y‖ + ‖ent P x (eI j)‖ * ‖ent G (eI i) y‖ := by
  have h : ent (P * (deltaW i j * G)) x y =
      ∑ c, ∑ d, (ent P x (eI c) * ent G (eI d) y) * deltaW i j c d := by
    rw [highOrder_ent_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [highOrder_ent_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ent_eI_eI]
    ring
  rw [h]
  refine (highOrder_norm_sum_delta _ i j).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul]

/-- The coefficient bounds of the resolvent expansion in the entry `(i, j)`: if
`|G_{ab}| ≤ B` and `R_s = |G_{vs}|`, then `|a_k| ≤ (2B)^{k−1} (R_i + R_j)²` for `k ≥ 1`
and `|a_1| ≤ 2 R_i R_j`. -/
private lemma highOrder_coeff_bound {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i j : Fin N)
    {B : ℝ} (hB : ∀ a b, ‖ent (GW A Wm z) (eI a) (eI b)‖ ≤ B) (k : ℕ) :
    ‖resCoeffW A Wm z v i j (k + 1)‖ ≤ (2 * B) ^ k *
      (‖ent (GW A Wm z) v (eI i)‖ + ‖ent (GW A Wm z) v (eI j)‖) ^ 2 ∧
    ‖resCoeffW A Wm z v i j 1‖ ≤
      2 * (‖ent (GW A Wm z) v (eI i)‖ * ‖ent (GW A Wm z) v (eI j)‖) := by
  set G := GW A Wm z with hGdef
  set Ri := ‖ent G v (eI i)‖ with hRi
  set Rj := ‖ent G v (eI j)‖ with hRj
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i i)
  have hsym : ∀ c, ‖ent G (eI c) v‖ = ‖ent G v (eI c)‖ := fun c => by
    rw [hGdef, highOrder_ent_symm hA hW hz]
  set M : ℕ → Matrix (Fin N) (Fin N) ℂ := fun k => G * (deltaW i j * G) ^ k with hM
  have hMs : ∀ k, M (k + 1) = M k * (deltaW i j * G) := fun k => by
    simp only [hM, pow_succ, Matrix.mul_assoc]
  have hM0 : M 0 = G := by simp [hM]
  have hres : ∀ k, ‖resCoeffW A Wm z v i j (k + 1)‖ = ‖ent (M (k + 1)) v v‖ := fun k => by
    simp [resCoeffW, hM, hGdef]
  have hS : ∀ k, ‖ent (M k) v (eI i)‖ + ‖ent (M k) v (eI j)‖ ≤ (2 * B) ^ k * (Ri + Rj) := by
    intro k
    induction k with
    | zero => simp [hM0, hRi, hRj]
    | succ k ih =>
      have h1 : ∀ c, ‖ent (M (k + 1)) v (eI c)‖ ≤
          B * (‖ent (M k) v (eI i)‖ + ‖ent (M k) v (eI j)‖) := by
        intro c
        rw [hMs]
        refine (highOrder_norm_ent_delta _ _ i j v (eI c)).trans ?_
        have hj := hB j c
        have hi := hB i c
        have h0i := norm_nonneg (ent (M k) v (eI i))
        have h0j := norm_nonneg (ent (M k) v (eI j))
        nlinarith
      have h2 := add_le_add (h1 i) (h1 j)
      calc _ ≤ _ := h2
        _ = 2 * B * (‖ent (M k) v (eI i)‖ + ‖ent (M k) v (eI j)‖) := by ring
        _ ≤ 2 * B * ((2 * B) ^ k * (Ri + Rj)) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * B) ^ (k + 1) * (Ri + Rj) := by ring
  have hlast : ∀ k, ‖ent (M (k + 1)) v v‖ ≤
      ‖ent (M k) v (eI i)‖ * Rj + ‖ent (M k) v (eI j)‖ * Ri := by
    intro k
    rw [hMs]
    refine (highOrder_norm_ent_delta _ _ i j v v).trans (le_of_eq ?_)
    rw [hsym, hsym]
  refine ⟨?_, ?_⟩
  · rw [hres]
    refine (hlast k).trans ?_
    have h0i := norm_nonneg (ent (M k) v (eI i))
    have h0j := norm_nonneg (ent (M k) v (eI j))
    have hRi0 : 0 ≤ Ri := norm_nonneg _
    have hRj0 : 0 ≤ Rj := norm_nonneg _
    calc ‖ent (M k) v (eI i)‖ * Rj + ‖ent (M k) v (eI j)‖ * Ri
        ≤ (‖ent (M k) v (eI i)‖ + ‖ent (M k) v (eI j)‖) * (Ri + Rj) := by nlinarith
      _ ≤ ((2 * B) ^ k * (Ri + Rj)) * (Ri + Rj) :=
          mul_le_mul_of_nonneg_right (hS k) (by positivity)
      _ = (2 * B) ^ k * (Ri + Rj) ^ 2 := by ring
  · have h := hres 0
    rw [zero_add] at h
    rw [h]
    refine (hlast 0).trans (le_of_eq ?_)
    rw [hM0]
    ring

/-! ## Counting in the tuples of the Leibniz expansion -/

/-- For `κ : Fin p → ℕ`: the number of zero entries `p − q`, of nonzero entries `q`, and of
entries equal to `1`, with `n = ∑ κ`: `q ≤ n`, `t ≤ n`, `2q ≤ n + t` and `q ≥ 1` if `n ≥ 1`. -/
private lemma highOrder_count {p : ℕ} (κ : Fin p → ℕ) :
    (∑ r, if κ r = 0 then 1 else 0) + (∑ r, if κ r = 0 then 0 else 1) = p ∧
    (∑ r, if κ r = 0 then 0 else 1) ≤ (∑ r, κ r) ∧
    (∑ r, if κ r = 1 then 1 else 0) ≤ (∑ r, κ r) ∧
    2 * (∑ r, if κ r = 0 then 0 else 1) ≤ (∑ r, κ r) + (∑ r, if κ r = 1 then 1 else 0) ∧
    (1 ≤ (∑ r, κ r) → 1 ≤ ∑ r, if κ r = 0 then 0 else 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_add_distrib]
    have : ∀ r, ((if κ r = 0 then 1 else 0) + if κ r = 0 then 0 else 1) = 1 := fun r => by
      split_ifs <;> rfl
    simp [this]
  · exact Finset.sum_le_sum fun r _ => by split_ifs <;> omega
  · exact Finset.sum_le_sum fun r _ => by split_ifs <;> omega
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => by split_ifs <;> omega
  · intro h
    by_contra hq
    push Not at hq
    have h0 : ∀ r ∈ Finset.univ, (if κ r = 0 then 0 else 1) = 0 :=
      (Finset.sum_eq_zero_iff).1 (by omega)
    have : ∑ r, κ r = 0 := Finset.sum_eq_zero fun r hr => by
      have := h0 r hr
      split_ifs at this with h'
      exact h'
    omega

/-- Product bound for the tuples with few nonzero entries: if `x_r ≤ F` when `κ_r = 0` and
`x_r ≤ c^{κ_r} P` otherwise, then `∏ x ≤ F^{p−q} c^n P^q`. -/
private lemma highOrder_prod_A {p : ℕ} (κ : Fin p → ℕ) (x : Fin p → ℝ) {F c P : ℝ}
    (hx : ∀ r, 0 ≤ x r)
    (h0 : ∀ r, κ r = 0 → x r ≤ F) (h1 : ∀ r, κ r ≠ 0 → x r ≤ c ^ κ r * P) :
    ∏ r, x r ≤ F ^ (∑ r, if κ r = 0 then 1 else 0) * c ^ (∑ r, κ r) *
      P ^ (∑ r, if κ r = 0 then 0 else 1) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun r _ => hx r) fun r _ => ?_
  by_cases h : κ r = 0
  · simp only [h, ite_true, pow_one, pow_zero, mul_one]
    exact h0 r h
  · simp only [h, ite_false, pow_zero, one_mul, pow_one]
    exact h1 r h

/-- Product bound for the tuples with many nonzero entries: if `x_r ≤ F` when `κ_r = 0`,
`x_r ≤ w` when `κ_r = 1` and `x_r ≤ c^{2κ_r}` when `κ_r ≥ 2` (`c ≥ 1`), then
`∏ x ≤ F^{p−q} c^{2n} w^t`. -/
private lemma highOrder_prod_B {p : ℕ} (κ : Fin p → ℕ) (x : Fin p → ℝ) {F c w : ℝ}
    (hc : 1 ≤ c) (hw : 0 ≤ w) (hx : ∀ r, 0 ≤ x r)
    (h0 : ∀ r, κ r = 0 → x r ≤ F) (h1 : ∀ r, κ r = 1 → x r ≤ w)
    (h2 : ∀ r, 2 ≤ κ r → x r ≤ c ^ (2 * κ r)) :
    ∏ r, x r ≤ F ^ (∑ r, if κ r = 0 then 1 else 0) * c ^ (2 * ∑ r, κ r) *
      w ^ (∑ r, if κ r = 1 then 1 else 0) := by
  rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun r _ => hx r) fun r _ => ?_
  by_cases h : κ r = 0
  · simp only [h, ite_true, pow_one, mul_zero, pow_zero, mul_one, zero_ne_one, ite_false]
    exact h0 r h
  · by_cases h' : κ r = 1
    · simp only [h', one_ne_zero, ite_false, ite_true, pow_zero, one_mul, pow_one, mul_one]
      calc x r ≤ w := h1 r h'
        _ ≤ c ^ 2 * w := le_mul_of_one_le_left hw (one_le_pow₀ hc)
    · simp only [h, h', ite_false, pow_zero, one_mul, mul_one]
      exact h2 r (by omega)

/-- `∑_{i ≤ j} f_{ij} ≤ ∑_{i,j} f_{ij}` for `f ≥ 0`. -/
private lemma highOrder_sum_upper_le {N : ℕ} (f : Fin N → Fin N → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    ∑ α : UpperIdx N, f α.1.1 α.1.2 ≤ ∑ i, ∑ j, f i j := by
  rw [← Fintype.sum_prod_type']
  have h : ∑ α : UpperIdx N, f α.1.1 α.1.2 =
      ∑ q ∈ Finset.univ.map (Function.Embedding.subtype fun q : Fin N × Fin N => q.1 ≤ q.2),
        f q.1 q.2 := by
    rw [Finset.sum_map]; rfl
  rw [h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => hf q.1 q.2

/-! ## Exponent arithmetic -/

/-- The case `q ≤ n − 2`, `n = n' + 4`: with `s = N^{−1/2} ≤ k₀ Ψ`, `s⁴ N² = 1`, `e⁴ ≤ d`,
`d^{30} ≤ g`, `g Ψ ≤ 1`, `B = e² d² Q`, `W ≤ N e² g d Ψ²` and the constant at most `d`:
`s^n (2B)^{n+2q−2} 4 N W ≤ (g Ψ)^q`. -/
private lemma highOrder_arith_A {n' q : ℕ} (hq : q ≤ n' + 2) {s Nr Ψ g d e Q k₀ W : ℝ}
    (hs0 : 0 ≤ s) (hsN : s ^ 4 * Nr ^ 2 = 1) (hNr : 0 ≤ Nr) (hΨ : 0 ≤ Ψ) (hd1 : 1 ≤ d)
    (he1 : 1 ≤ e) (he : e ^ 4 ≤ d) (hg : d ^ 30 ≤ g) (hgΨ : g * Ψ ≤ 1) (hsi : s ≤ k₀ * Ψ)
    (hQ : 1 ≤ Q) (hW0 : 0 ≤ W) (hW : W ≤ Nr * (e ^ 2 * (g * d) * Ψ ^ 2))
    (hK : 4 * k₀ ^ n' * (2 * Q) ^ (3 * n' + 6) ≤ d) :
    s ^ (n' + 4) * ((2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * q + 2) * (4 * Nr * W)) ≤
      (g * Ψ) ^ q := by
  have hd0 : 0 ≤ d := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  have he2 : e ^ 2 ≤ d := le_trans (pow_le_pow_right₀ he1 (by norm_num)) he
  have hB1 : 1 ≤ 2 * (e ^ 2 * d ^ 2 * Q) := by
    have : 1 ≤ e ^ 2 * d ^ 2 * Q :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he1)
        (one_le_pow₀ hd1)) hQ
    linarith
  have h1 : (2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * q + 2) ≤
      (2 * Q) ^ (3 * n' + 6) * d ^ (9 * n' + 18) := by
    calc (2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * q + 2)
        ≤ (2 * (e ^ 2 * d ^ 2 * Q)) ^ (3 * n' + 6) := pow_le_pow_right₀ hB1 (by omega)
      _ = (2 * Q) ^ (3 * n' + 6) * (e ^ 2 * d ^ 2) ^ (3 * n' + 6) := by
          rw [← mul_pow]; ring_nf
      _ ≤ (2 * Q) ^ (3 * n' + 6) * (d * d ^ 2) ^ (3 * n' + 6) := by gcongr
      _ = (2 * Q) ^ (3 * n' + 6) * d ^ (9 * n' + 18) := by rw [← pow_succ', ← pow_mul]; ring_nf
  have h2 : s ^ (n' + 4) * (4 * Nr * W) ≤ 4 * (k₀ ^ n' * Ψ ^ n') * (e ^ 2 * (g * d) * Ψ ^ 2) := by
    have hsn : s ^ n' ≤ k₀ ^ n' * Ψ ^ n' := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hs0 hsi n'
    calc s ^ (n' + 4) * (4 * Nr * W) ≤ s ^ (n' + 4) * (4 * Nr * (Nr * (e ^ 2 * (g * d) * Ψ ^ 2))) :=
          by gcongr
      _ = 4 * s ^ n' * (s ^ 4 * Nr ^ 2) * (e ^ 2 * (g * d) * Ψ ^ 2) := by ring
      _ = 4 * s ^ n' * (e ^ 2 * (g * d) * Ψ ^ 2) := by rw [hsN, mul_one]
      _ ≤ 4 * (k₀ ^ n' * Ψ ^ n') * (e ^ 2 * (g * d) * Ψ ^ 2) := by gcongr
  have hgΨ0 : 0 ≤ g * Ψ := mul_nonneg hg0 hΨ
  have h3 : d ^ (9 * n' + 21) ≤ g ^ (n' + 1) := by
    calc d ^ (9 * n' + 21) ≤ d ^ (30 * (n' + 1)) := pow_le_pow_right₀ hd1 (by omega)
      _ = (d ^ 30) ^ (n' + 1) := by rw [pow_mul]
      _ ≤ g ^ (n' + 1) := pow_le_pow_left₀ (by positivity) hg _
  calc s ^ (n' + 4) * ((2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * q + 2) * (4 * Nr * W))
      = (2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * q + 2) * (s ^ (n' + 4) * (4 * Nr * W)) := by ring
    _ ≤ ((2 * Q) ^ (3 * n' + 6) * d ^ (9 * n' + 18)) *
          (4 * (k₀ ^ n' * Ψ ^ n') * (e ^ 2 * (g * d) * Ψ ^ 2)) := by
        gcongr
    _ = (4 * k₀ ^ n' * (2 * Q) ^ (3 * n' + 6)) * e ^ 2 * (d ^ (9 * n' + 19) * g * Ψ ^ (n' + 2)) :=
        by ring
    _ ≤ d * d * (d ^ (9 * n' + 19) * g * Ψ ^ (n' + 2)) := by gcongr
    _ = d ^ (9 * n' + 21) * g * Ψ ^ (n' + 2) := by ring
    _ ≤ g ^ (n' + 1) * g * Ψ ^ (n' + 2) := by gcongr
    _ = (g * Ψ) ^ (n' + 2) := by ring
    _ ≤ (g * Ψ) ^ q := pow_le_pow_of_le_one hgΨ0 hgΨ hq

/-- The case `q ≥ n − 1`, `n = n' + 4` (two entries equal to `1`), with the hypotheses of the
case `q ≤ n − 2`: `s^n 4 (2B)^{4n−4} W² ≤ (g Ψ)^q`. -/
private lemma highOrder_arith_B {n' q : ℕ} (hq : q ≤ n' + 4) {s Nr Ψ g d e Q k₀ W : ℝ}
    (hs0 : 0 ≤ s) (hsN : s ^ 4 * Nr ^ 2 = 1) (hΨ : 0 ≤ Ψ) (hd1 : 1 ≤ d)
    (he1 : 1 ≤ e) (he : e ^ 4 ≤ d) (hg : d ^ 30 ≤ g) (hgΨ : g * Ψ ≤ 1) (hsi : s ≤ k₀ * Ψ)
    (hk₀ : 0 ≤ k₀) (hQ : 1 ≤ Q) (hW0 : 0 ≤ W) (hW : W ≤ Nr * (e ^ 2 * (g * d) * Ψ ^ 2))
    (hK : 4 * k₀ ^ n' * (2 * Q) ^ (4 * n' + 12) ≤ d) :
    s ^ (n' + 4) * (4 * (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12) * W ^ 2) ≤ (g * Ψ) ^ q := by
  have hd0 : 0 ≤ d := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  have he2 : e ^ 2 ≤ d := le_trans (pow_le_pow_right₀ he1 (by norm_num)) he
  have h1 : (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12) ≤
      (2 * Q) ^ (4 * n' + 12) * d ^ (12 * n' + 36) := by
    calc (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12)
        = (2 * Q) ^ (4 * n' + 12) * (e ^ 2 * d ^ 2) ^ (4 * n' + 12) := by
          rw [← mul_pow]; ring_nf
      _ ≤ (2 * Q) ^ (4 * n' + 12) * (d * d ^ 2) ^ (4 * n' + 12) := by gcongr
      _ = (2 * Q) ^ (4 * n' + 12) * d ^ (12 * n' + 36) := by
          rw [← pow_succ', ← pow_mul]; ring_nf
  have h2 : s ^ (n' + 4) * W ^ 2 ≤ (k₀ ^ n' * Ψ ^ n') * (d * g ^ 2 * d ^ 2 * Ψ ^ 4) := by
    have hsn : s ^ n' ≤ k₀ ^ n' * Ψ ^ n' := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hs0 hsi n'
    have hW2 : W ^ 2 ≤ (Nr * (e ^ 2 * (g * d) * Ψ ^ 2)) ^ 2 := pow_le_pow_left₀ hW0 hW 2
    calc s ^ (n' + 4) * W ^ 2 ≤ s ^ (n' + 4) * (Nr * (e ^ 2 * (g * d) * Ψ ^ 2)) ^ 2 := by gcongr
      _ = s ^ n' * (s ^ 4 * Nr ^ 2) * (e ^ 4 * g ^ 2 * d ^ 2 * Ψ ^ 4) := by ring
      _ = s ^ n' * (e ^ 4 * g ^ 2 * d ^ 2 * Ψ ^ 4) := by rw [hsN, mul_one]
      _ ≤ (k₀ ^ n' * Ψ ^ n') * (d * g ^ 2 * d ^ 2 * Ψ ^ 4) := by
          refine mul_le_mul hsn ?_ (by positivity) (by positivity)
          gcongr
  have hgΨ0 : 0 ≤ g * Ψ := mul_nonneg hg0 hΨ
  have h3 : d ^ (12 * n' + 40) ≤ g ^ (n' + 2) := by
    calc d ^ (12 * n' + 40) ≤ d ^ (30 * (n' + 2)) := pow_le_pow_right₀ hd1 (by omega)
      _ = (d ^ 30) ^ (n' + 2) := by rw [pow_mul]
      _ ≤ g ^ (n' + 2) := pow_le_pow_left₀ (by positivity) hg _
  calc s ^ (n' + 4) * (4 * (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12) * W ^ 2)
      = 4 * (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12) * (s ^ (n' + 4) * W ^ 2) := by ring
    _ ≤ 4 * ((2 * Q) ^ (4 * n' + 12) * d ^ (12 * n' + 36)) *
          ((k₀ ^ n' * Ψ ^ n') * (d * g ^ 2 * d ^ 2 * Ψ ^ 4)) := by
        gcongr
    _ = (4 * k₀ ^ n' * (2 * Q) ^ (4 * n' + 12)) * (d ^ (12 * n' + 39) * g ^ 2 * Ψ ^ (n' + 4)) :=
        by ring
    _ ≤ d * (d ^ (12 * n' + 39) * g ^ 2 * Ψ ^ (n' + 4)) := by gcongr
    _ = d ^ (12 * n' + 40) * g ^ 2 * Ψ ^ (n' + 4) := by ring
    _ ≤ g ^ (n' + 2) * g ^ 2 * Ψ ^ (n' + 4) := by gcongr
    _ = (g * Ψ) ^ (n' + 4) := by ring
    _ ≤ (g * Ψ) ^ q := pow_le_pow_of_le_one hgΨ0 hgΨ hq

/-! ## Bounds on the a priori event -/

/-- `a_0 = (G − Π)_{vv}`, so `|a_0| = F_v`. -/
private lemma highOrder_norm_coeff_zero {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) : ‖resCoeffW A Wm z v i j 0‖ = FvW A Wm z v := by
  simp [resCoeffW, FvW]

/-- On the a priori event, for a tuple `κ` with `∑ κ = n` and `q ≤ n − 2` nonzero entries:
`∑_{i ≤ j} ∏_r |a_{κ_r}| ≤ F_v^{p−q} (2B)^{n+2q−2} 4 N W`, where `|G_{ab}|, |G_{vs}| ≤ B` and
`W ≥ ∑_s |G_{vs}|²`. -/
private lemma highOrder_event_A {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) {p : ℕ} (κ : Fin p → ℕ)
    (hq1 : 1 ≤ ∑ r, if κ r = 0 then 0 else 1) {B Wb : ℝ} (hB : 1 ≤ 2 * B)
    (hGab : ∀ a b, ‖ent (GW A Wm z) (eI a) (eI b)‖ ≤ B)
    (hR : ∀ c, ‖ent (GW A Wm z) v (eI c)‖ ≤ B)
    (hWb : ∑ s, ‖ent (GW A Wm z) v (eI s)‖ ^ 2 ≤ Wb) :
    ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖ ≤
      FvW A Wm z v ^ (∑ r, if κ r = 0 then 1 else 0) *
        ((2 * B) ^ ((∑ r, κ r) + 2 * (∑ r, if κ r = 0 then 0 else 1) - 2) * (4 * N * Wb)) := by
  set G := GW A Wm z with hGdef
  set F := FvW A Wm z v with hFdef
  set R : Fin N → ℝ := fun c => ‖ent G v (eI c)‖ with hRdef
  set qc := ∑ r, if κ r = 0 then 0 else 1 with hqc
  set n := ∑ r, κ r with hn
  have hF0 : 0 ≤ F := norm_nonneg _
  have hB0 : 0 ≤ 2 * B := by linarith
  have hR0 : ∀ c, 0 ≤ R c := fun c => norm_nonneg _
  have hper : ∀ i j : Fin N, ∏ r, ‖resCoeffW A Wm z v i j (κ r)‖ ≤
      F ^ (∑ r, if κ r = 0 then 1 else 0) * ((2 * B) ^ (n + 2 * qc - 2) * (R i + R j) ^ 2) := by
    intro i j
    have hP0 : 0 ≤ (R i + R j) ^ 2 := sq_nonneg _
    have hPB : (R i + R j) ^ 2 ≤ (2 * B) ^ 2 := by
      have := add_le_add (hR i) (hR j)
      exact pow_le_pow_left₀ (add_nonneg (hR0 i) (hR0 j)) (by simp only [hRdef]; linarith) 2
    have h := highOrder_prod_A κ (fun r => ‖resCoeffW A Wm z v i j (κ r)‖) (c := 2 * B)
      (P := (R i + R j) ^ 2) (F := F) (fun r => norm_nonneg _)
      (fun r hr => by simp only [hr, highOrder_norm_coeff_zero, hFdef]; exact le_rfl)
      (fun r hr => by
        obtain ⟨k, hk⟩ : ∃ k, κ r = k + 1 := ⟨κ r - 1, by omega⟩
        simp only [hk]
        refine ((highOrder_coeff_bound hA hW hz v i j hGab k).1).trans ?_
        rw [pow_succ]
        have : (2 * B) ^ k * (R i + R j) ^ 2 ≤ (2 * B) ^ k * 2 * B * (R i + R j) ^ 2 := by
          have h0 : 0 ≤ (2 * B) ^ k * (R i + R j) ^ 2 := by positivity
          nlinarith
        calc (2 * B) ^ k * (‖ent (GW A Wm z) v (eI i)‖ + ‖ent (GW A Wm z) v (eI j)‖) ^ 2
            = (2 * B) ^ k * (R i + R j) ^ 2 := rfl
          _ ≤ (2 * B) ^ k * 2 * B * (R i + R j) ^ 2 := this
          _ = (2 * B) ^ k * (2 * B) * (R i + R j) ^ 2 := by ring)
    refine h.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hF0 _)
    have key : ∀ m q : ℕ, 1 ≤ q → (2 * B) ^ m * ((R i + R j) ^ 2) ^ q ≤
        (2 * B) ^ (m + 2 * q - 2) * (R i + R j) ^ 2 := by
      intro m q hq
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      calc (2 * B) ^ m * ((R i + R j) ^ 2) ^ (q' + 1)
          = (2 * B) ^ m * (((R i + R j) ^ 2) ^ q' * (R i + R j) ^ 2) := by rw [pow_succ]
        _ ≤ (2 * B) ^ m * (((2 * B) ^ 2) ^ q' * (R i + R j) ^ 2) := by gcongr
        _ = (2 * B) ^ (m + 2 * (q' + 1) - 2) * (R i + R j) ^ 2 := by
            rw [← pow_mul, ← mul_assoc, ← pow_add]
            congr 2
    exact key _ _ hq1
  calc ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖
      ≤ ∑ α : UpperIdx N, F ^ (∑ r, if κ r = 0 then 1 else 0) *
          ((2 * B) ^ (n + 2 * qc - 2) * (R α.1.1 + R α.1.2) ^ 2) :=
        Finset.sum_le_sum fun α _ => hper α.1.1 α.1.2
    _ ≤ ∑ i, ∑ j, F ^ (∑ r, if κ r = 0 then 1 else 0) *
          ((2 * B) ^ (n + 2 * qc - 2) * (R i + R j) ^ 2) :=
        highOrder_sum_upper_le (fun i j => F ^ (∑ r, if κ r = 0 then 1 else 0) *
          ((2 * B) ^ (n + 2 * qc - 2) * (R i + R j) ^ 2)) fun i j => by positivity
    _ = F ^ (∑ r, if κ r = 0 then 1 else 0) * ((2 * B) ^ (n + 2 * qc - 2) *
          ∑ i, ∑ j, (R i + R j) ^ 2) := by
        simp only [Finset.mul_sum]
    _ ≤ F ^ (∑ r, if κ r = 0 then 1 else 0) * ((2 * B) ^ (n + 2 * qc - 2) * (4 * N * Wb)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hB0 _))
          (pow_nonneg hF0 _)
        have h1 : ∑ i, ∑ j, (R i + R j) ^ 2 ≤ ∑ i, ∑ j, (2 * R i ^ 2 + 2 * R j ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            nlinarith [sq_nonneg (R i - R j)]
        have h2 : ∑ i : Fin N, ∑ j : Fin N, (2 * R i ^ 2 + 2 * R j ^ 2) =
            4 * N * ∑ s, R s ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          ring
        have h3 : ∑ s, R s ^ 2 ≤ Wb := hWb
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        calc _ ≤ _ := h1
          _ = 4 * N * ∑ s, R s ^ 2 := h2
          _ ≤ 4 * N * Wb := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- On the a priori event, for a tuple `κ` with `∑ κ = n` and at least two entries equal to `1`:
`∑_{i ≤ j} ∏_r |a_{κ_r}| ≤ F_v^{p−q} 4 (2B)^{4n−4} W²`. -/
private lemma highOrder_event_B {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) {p : ℕ} (κ : Fin p → ℕ)
    (ht2 : 2 ≤ ∑ r, if κ r = 1 then 1 else 0)
    (htn : (∑ r, if κ r = 1 then 1 else 0) ≤ ∑ r, κ r) {B Wb : ℝ} (hB : 1 ≤ 2 * B)
    (hGab : ∀ a b, ‖ent (GW A Wm z) (eI a) (eI b)‖ ≤ B)
    (hR : ∀ c, ‖ent (GW A Wm z) v (eI c)‖ ≤ B)
    (hWb : ∑ s, ‖ent (GW A Wm z) v (eI s)‖ ^ 2 ≤ Wb) :
    ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖ ≤
      FvW A Wm z v ^ (∑ r, if κ r = 0 then 1 else 0) *
        (4 * (2 * B) ^ (4 * (∑ r, κ r) - 4) * Wb ^ 2) := by
  set G := GW A Wm z with hGdef
  set F := FvW A Wm z v with hFdef
  set R : Fin N → ℝ := fun c => ‖ent G v (eI c)‖ with hRdef
  set tc := ∑ r, if κ r = 1 then 1 else 0 with htc
  set n := ∑ r, κ r with hn
  have hF0 : 0 ≤ F := norm_nonneg _
  have hB0 : 0 ≤ 2 * B := by linarith
  have hR0 : ∀ c, 0 ≤ R c := fun c => norm_nonneg _
  have hRB : ∀ c, R c ≤ B := hR
  have hper : ∀ i j : Fin N, ∏ r, ‖resCoeffW A Wm z v i j (κ r)‖ ≤
      F ^ (∑ r, if κ r = 0 then 1 else 0) * (4 * (2 * B) ^ (4 * n - 4) * (R i * R j) ^ 2) := by
    intro i j
    have hPB : (R i + R j) ^ 2 ≤ (2 * B) ^ 2 :=
      pow_le_pow_left₀ (add_nonneg (hR0 i) (hR0 j)) (by linarith [hRB i, hRB j]) 2
    have hQ0 : 0 ≤ 2 * (R i * R j) := by have := hR0 i; have := hR0 j; positivity
    have hQB : 2 * (R i * R j) ≤ (2 * B) ^ 2 := by
      have := mul_le_mul (hRB i) (hRB j) (hR0 j) (by linarith [hR0 i, hRB i])
      nlinarith
    have h := highOrder_prod_B κ (fun r => ‖resCoeffW A Wm z v i j (κ r)‖) (c := 2 * B)
      (w := 2 * (R i * R j)) (F := F) hB hQ0 (fun r => norm_nonneg _)
      (fun r hr => by simp only [hr, highOrder_norm_coeff_zero, hFdef]; exact le_rfl)
      (fun r hr => by
        simp only [hr]
        exact (highOrder_coeff_bound hA hW hz v i j hGab 0).2)
      (fun r hr => by
        obtain ⟨k, hk⟩ : ∃ k, κ r = k + 1 := ⟨κ r - 1, by omega⟩
        simp only [hk]
        refine ((highOrder_coeff_bound hA hW hz v i j hGab k).1).trans ?_
        calc (2 * B) ^ k * (‖ent (GW A Wm z) v (eI i)‖ + ‖ent (GW A Wm z) v (eI j)‖) ^ 2
            = (2 * B) ^ k * (R i + R j) ^ 2 := rfl
          _ ≤ (2 * B) ^ k * (2 * B) ^ 2 := mul_le_mul_of_nonneg_left hPB (by positivity)
          _ = (2 * B) ^ (k + 2) := by rw [← pow_add]
          _ ≤ (2 * B) ^ (2 * (k + 1)) := pow_le_pow_right₀ hB (by omega))
    refine h.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hF0 _)
    have key : ∀ m t : ℕ, 2 ≤ t → t ≤ m → (2 * B) ^ (2 * m) * (2 * (R i * R j)) ^ t ≤
        4 * (2 * B) ^ (4 * m - 4) * (R i * R j) ^ 2 := by
      intro m t ht htm
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
      calc (2 * B) ^ (2 * m) * (2 * (R i * R j)) ^ (t' + 2)
          = (2 * B) ^ (2 * m) * ((2 * (R i * R j)) ^ t' * (2 * (R i * R j)) ^ 2) := by
            rw [pow_add]
        _ ≤ (2 * B) ^ (2 * m) * (((2 * B) ^ 2) ^ t' * (2 * (R i * R j)) ^ 2) := by gcongr
        _ = 4 * ((2 * B) ^ (2 * m + 2 * t') * (R i * R j) ^ 2) := by
            rw [← pow_mul, pow_add]; ring
        _ ≤ 4 * ((2 * B) ^ (4 * m - 4) * (R i * R j) ^ 2) := by
            gcongr
            omega
        _ = 4 * (2 * B) ^ (4 * m - 4) * (R i * R j) ^ 2 := by ring
    exact key _ _ ht2 htn
  calc ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖
      ≤ ∑ α : UpperIdx N, F ^ (∑ r, if κ r = 0 then 1 else 0) *
          (4 * (2 * B) ^ (4 * n - 4) * (R α.1.1 * R α.1.2) ^ 2) :=
        Finset.sum_le_sum fun α _ => hper α.1.1 α.1.2
    _ ≤ ∑ i, ∑ j, F ^ (∑ r, if κ r = 0 then 1 else 0) *
          (4 * (2 * B) ^ (4 * n - 4) * (R i * R j) ^ 2) :=
        highOrder_sum_upper_le (fun i j => F ^ (∑ r, if κ r = 0 then 1 else 0) *
          (4 * (2 * B) ^ (4 * n - 4) * (R i * R j) ^ 2)) fun i j => by positivity
    _ = F ^ (∑ r, if κ r = 0 then 1 else 0) * (4 * (2 * B) ^ (4 * n - 4) *
          ((∑ s, R s ^ 2) * (∑ s, R s ^ 2))) := by
        rw [Finset.sum_mul_sum]
        simp only [Finset.mul_sum, mul_pow]
    _ ≤ F ^ (∑ r, if κ r = 0 then 1 else 0) * (4 * (2 * B) ^ (4 * n - 4) * Wb ^ 2) := by
        have h0 : 0 ≤ ∑ s, R s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
        have h3 : ∑ s, R s ^ 2 ≤ Wb := hWb
        have h4 : (∑ s, R s ^ 2) * (∑ s, R s ^ 2) ≤ Wb ^ 2 := by nlinarith
        gcongr

/-- For one tuple `κ` with `∑ κ = n ∈ [4, 4p]`, on the a priori event (entries at most
`B = e² d² Q`, `∑_s |G_{vs}|² ≤ N e² g d Ψ²`): `s^n ∑_{i ≤ j} ∏_r |a_{κ_r}| ≤ F_v^p + (g Ψ)^p`
(the two cases `q ≤ n − 2` and `q ≥ n − 1`, then Young). -/
private lemma highOrder_event_tuple {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) {p n : ℕ}
    (hp : 0 < p) (hn4 : 4 ≤ n) (κ : Fin p → ℕ) (hκ : ∑ r, κ r = n) {s Ψ g d e Q k₀ : ℝ}
    (hs0 : 0 ≤ s) (hsN : s ^ 4 * (N : ℝ) ^ 2 = 1) (hΨ : 0 ≤ Ψ) (hd1 : 1 ≤ d) (he1 : 1 ≤ e)
    (he : e ^ 4 ≤ d) (hg : d ^ 30 ≤ g) (hgΨ : g * Ψ ≤ 1) (hsi : s ≤ k₀ * Ψ) (hk₀ : 0 ≤ k₀)
    (hQ : 1 ≤ Q) (hK : 4 * k₀ ^ (n - 4) * (2 * Q) ^ (4 * n) ≤ d)
    (hGab : ∀ a b, ‖ent (GW A Wm z) (eI a) (eI b)‖ ≤ e ^ 2 * d ^ 2 * Q)
    (hR : ∀ c, ‖ent (GW A Wm z) v (eI c)‖ ≤ e ^ 2 * d ^ 2 * Q)
    (hWb : ∑ s, ‖ent (GW A Wm z) v (eI s)‖ ^ 2 ≤ N * (e ^ 2 * (g * d) * Ψ ^ 2)) :
    s ^ n * ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖ ≤
      FvW A Wm z v ^ p + (g * Ψ) ^ p := by
  obtain ⟨hzq, hqn, htn, h2q, hq1⟩ := highOrder_count κ
  rw [hκ] at hqn htn h2q hq1
  have hq1' := hq1 (by omega)
  set qc := ∑ r, if κ r = 0 then 0 else 1 with hqc
  set zc := ∑ r, if κ r = 0 then 1 else 0 with hzc
  set tc := ∑ r, if κ r = 1 then 1 else 0 with htc
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
  have hn' : n' + 4 - 4 = n' := by omega
  rw [hn'] at hK
  have hd0 : 0 ≤ d := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  have hB : 1 ≤ 2 * (e ^ 2 * d ^ 2 * Q) := by
    have : 1 ≤ e ^ 2 * d ^ 2 * Q :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he1)
        (one_le_pow₀ hd1)) hQ
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hWb0 : 0 ≤ (N : ℝ) * (e ^ 2 * (g * d) * Ψ ^ 2) := by positivity
  have hF0 : 0 ≤ FvW A Wm z v := norm_nonneg _
  have h2Q : 1 ≤ 2 * Q := by linarith
  have hmain : s ^ (n' + 4) * ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖ ≤
      FvW A Wm z v ^ zc * (g * Ψ) ^ qc := by
    by_cases hcase : qc ≤ n' + 2
    · have hev := highOrder_event_A hA hW hz v κ hq1' hB hGab hR hWb
      rw [hκ] at hev
      have hK' : 4 * k₀ ^ n' * (2 * Q) ^ (3 * n' + 6) ≤ d :=
        le_trans (by gcongr; omega) hK
      have har := highOrder_arith_A hcase hs0 hsN hN0 hΨ hd1 he1 he hg hgΨ hsi hQ hWb0 le_rfl hK'
      have hexp : n' + 4 + 2 * qc - 2 = n' + 2 * qc + 2 := by omega
      rw [hexp] at hev
      calc s ^ (n' + 4) * ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖
          ≤ s ^ (n' + 4) * (FvW A Wm z v ^ zc * ((2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * qc + 2) *
              (4 * N * (N * (e ^ 2 * (g * d) * Ψ ^ 2))))) :=
            mul_le_mul_of_nonneg_left hev (pow_nonneg hs0 _)
        _ = FvW A Wm z v ^ zc * (s ^ (n' + 4) * ((2 * (e ^ 2 * d ^ 2 * Q)) ^ (n' + 2 * qc + 2) *
              (4 * N * (N * (e ^ 2 * (g * d) * Ψ ^ 2))))) := by ring
        _ ≤ FvW A Wm z v ^ zc * (g * Ψ) ^ qc :=
            mul_le_mul_of_nonneg_left har (pow_nonneg hF0 _)
    · have ht2 : 2 ≤ tc := by omega
      have hev := highOrder_event_B hA hW hz v κ ht2 (by rw [hκ]; exact htn) hB hGab hR hWb
      rw [hκ] at hev
      have hK' : 4 * k₀ ^ n' * (2 * Q) ^ (4 * n' + 12) ≤ d :=
        le_trans (by gcongr; omega) hK
      have har := highOrder_arith_B (q := qc) (by omega) hs0 hsN hΨ hd1 he1 he hg hgΨ hsi hk₀ hQ
        hWb0 le_rfl hK'
      have hexp : 4 * (n' + 4) - 4 = 4 * n' + 12 := by omega
      rw [hexp] at hev
      calc s ^ (n' + 4) * ∑ α : UpperIdx N, ∏ r, ‖resCoeffW A Wm z v α.1.1 α.1.2 (κ r)‖
          ≤ s ^ (n' + 4) * (FvW A Wm z v ^ zc * (4 * (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12) *
              (N * (e ^ 2 * (g * d) * Ψ ^ 2)) ^ 2)) :=
            mul_le_mul_of_nonneg_left hev (pow_nonneg hs0 _)
        _ = FvW A Wm z v ^ zc * (s ^ (n' + 4) * (4 * (2 * (e ^ 2 * d ^ 2 * Q)) ^ (4 * n' + 12) *
              (N * (e ^ 2 * (g * d) * Ψ ^ 2)) ^ 2)) := by ring
        _ ≤ FvW A Wm z v ^ zc * (g * Ψ) ^ qc :=
            mul_le_mul_of_nonneg_left har (pow_nonneg hF0 _)
  refine hmain.trans ?_
  have hqp : qc ≤ p := by omega
  have hzc' : zc = p - qc := by omega
  rw [hzc']
  have hy := young_pow hF0 (mul_nonneg hg0 hΨ) hqp hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hw1 : ((p - qc : ℕ) : ℝ) / p ≤ 1 := by
    rw [div_le_one hp']; exact_mod_cast Nat.sub_le p qc
  have hw2 : (qc : ℝ) / p ≤ 1 := by
    rw [div_le_one hp']; exact_mod_cast hqp
  have hFp : 0 ≤ FvW A Wm z v ^ p := pow_nonneg hF0 p
  have hgp : 0 ≤ (g * Ψ) ^ p := pow_nonneg (mul_nonneg hg0 hΨ) p
  nlinarith [mul_le_mul_of_nonneg_right hw1 hFp, mul_le_mul_of_nonneg_right hw2 hgp]

/-! ## Deterministic bounds, measurability, the Leibniz expansion -/

/-- `|f_n| ≤ ∑_{κ ∈ T(p,n)} ∏_r |a_{κ_r}|`. -/
private lemma highOrder_norm_fCoeff_le (p n : ℕ) (a : ℕ → ℂ) :
    ‖fCoeff p a n‖ ≤ ∑ κ ∈ Finset.Nat.antidiagonalTuple p n, ∏ r : Fin p, ‖a (κ r)‖ := by
  unfold fCoeff
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_prod]
  refine le_of_eq (Finset.prod_congr rfl fun r _ => ?_)
  split_ifs
  · rfl
  · rw [Complex.norm_conj]

/-- `|T(p, n)| ≤ (n + 1)^p` for the tuples `κ : Fin p → ℕ` with `∑ κ = n`. -/
private lemma highOrder_card_tuple (p n : ℕ) :
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

/-- `G^W(z)` is a measurable function of the matrix `W`. -/
private lemma highOrder_measurable_GW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z := by
  refine Matrix.measurable_iff.2 fun s t => ?_
  have hc : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    unfold cplx
    exact ((continuous_id.add continuous_const).matrix_map Complex.continuous_ofReal).sub
      continuous_const
  have hdet : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    hc.matrix_det.measurable
  have hadj : Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t :=
    (Matrix.measurable_iff.1 hc.matrix_adjugate.measurable) s t
  have h : (fun Wm : Matrix (Fin N) (Fin N) ℝ => GW A Wm z s t) = fun Wm =>
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det⁻¹ *
        (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate s t := by
    funext Wm
    unfold GW
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [h]
  exact hdet.inv.mul hadj

/-- `x^T B y` is continuous in `B`. -/
private lemma highOrder_continuous_ent {N : ℕ} (x y : Fin N → ℝ) :
    Continuous fun B : Matrix (Fin N) (Fin N) ℂ => ent B x y := by
  unfold ent
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/-- `f_n` of the coefficients `a_k` is a continuous function of `G`. -/
private lemma highOrder_continuous_fCoeff {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (p n : ℕ) :
    Continuous fun G : Matrix (Fin N) (Fin N) ℂ => fCoeff p (fun k => (-1) ^ k *
      ent (G * (deltaW i j * G) ^ k - if k = 0 then piW A z else 0) v v) n := by
  have ha : ∀ k, Continuous fun G : Matrix (Fin N) (Fin N) ℂ => (-1 : ℂ) ^ k *
      ent (G * (deltaW i j * G) ^ k - if k = 0 then piW A z else 0) v v := fun k =>
    continuous_const.mul ((highOrder_continuous_ent v v).comp
      ((continuous_id.mul ((continuous_const.mul continuous_id).pow k)).sub continuous_const))
  unfold fCoeff
  refine continuous_finsetSum _ fun κ _ => continuous_finsetProd _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.comp (ha _)

/-- `ω ↦ |f_n(a(W(ω)))|` is measurable for measurable entries. -/
private lemma highOrder_measurable_coeff {Ω : Type*} [MeasureSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hWm : Measurable W) (A : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (v : Fin N → ℝ) (i j : Fin N) (p n : ℕ) :
    Measurable fun ω => ‖fCoeff p (resCoeffW A (W ω) z v i j) n‖ :=
  ((highOrder_continuous_fCoeff A z v i j p n).measurable.comp
    ((highOrder_measurable_GW A z).comp hWm)).norm

/-- `ω ↦ F_v(W(ω), z)` is measurable for measurable entries. -/
private lemma highOrder_measurable_Fv {Ω : Type*} [MeasureSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hWm : Measurable W) (A : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (v : Fin N → ℝ) : Measurable fun ω => FvW A (W ω) z v :=
  (((highOrder_continuous_ent v v).comp (continuous_id.sub continuous_const)).measurable.comp
    ((highOrder_measurable_GW A z).comp hWm)).norm

/-- `(B − C)_{xy} = B_{xy} − C_{xy}`. -/
private lemma highOrder_ent_sub {N : ℕ} (B C : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (B - C) x y = ent B x y - ent C x y := by
  simp only [ent, Matrix.sub_mulVec, dotProduct_sub]

/-- `|e_a| = 1`. -/
private lemma highOrder_testNorm_eI {N : ℕ} (a : Fin N) : testNorm (eI a) = 1 := by
  simp [testNorm, eI, Pi.single_apply]

/-- The deterministic bound `|f_n| ≤ (n + 1)^p ((2 + τ⁻¹) N)^{n+p}`, from `|G_{xy}| ≤ (Im z)⁻¹ ≤ N`
and `|Π_{vv}| ≤ τ⁻¹`. -/
private lemma highOrder_det_bound {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N)
    (hN1 : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {v : Fin N → ℝ} (hv : testNorm v = 1)
    (hPi : ‖ent (piW A z) v v‖ ≤ τ⁻¹) (i j : Fin N) (p n : ℕ) :
    ‖fCoeff p (resCoeffW A Wm z v i j) n‖ ≤ ((n : ℝ) + 1) ^ p * ((2 + τ⁻¹) * N) ^ (n + p) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hηi : 0 < z.im⁻¹ := inv_pos.2 hz
  have hL1 : 1 ≤ (2 + τ⁻¹) * N := by nlinarith
  have hGab : ∀ a b, ‖ent (GW A Wm z) (eI a) (eI b)‖ ≤ z.im⁻¹ := fun a b => by
    have := highOrder_norm_ent_le hA hW hz (eI a) (eI b)
    rwa [highOrder_testNorm_eI, highOrder_testNorm_eI, mul_one, mul_one] at this
  have hR : ∀ c, ‖ent (GW A Wm z) v (eI c)‖ ≤ z.im⁻¹ := fun c => by
    have := highOrder_norm_ent_le hA hW hz v (eI c)
    rwa [hv, highOrder_testNorm_eI, mul_one, mul_one] at this
  refine norm_fCoeff_le p hL1 n fun k _ => ?_
  rcases k with _ | k
  · rw [highOrder_norm_coeff_zero, FvW, highOrder_ent_sub]
    have h1 := highOrder_norm_ent_le hA hW hz v v
    rw [hv, mul_one, mul_one] at h1
    calc ‖ent (GW A Wm z) v v - ent (piW A z) v v‖
        ≤ ‖ent (GW A Wm z) v v‖ + ‖ent (piW A z) v v‖ := norm_sub_le _ _
      _ ≤ N + τ⁻¹ := add_le_add (h1.trans hηN) hPi
      _ ≤ ((2 + τ⁻¹) * N) ^ (0 + 1) := by rw [zero_add, pow_one]; nlinarith
  · refine ((highOrder_coeff_bound hA hW hz v i j hGab k).1).trans ?_
    have h2 : (‖ent (GW A Wm z) v (eI i)‖ + ‖ent (GW A Wm z) v (eI j)‖) ^ 2 ≤
        (2 * z.im⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [hR i, hR j]) 2
    have h3 : 2 * z.im⁻¹ ≤ (2 + τ⁻¹) * N := by nlinarith
    calc (2 * z.im⁻¹) ^ k * (‖ent (GW A Wm z) v (eI i)‖ + ‖ent (GW A Wm z) v (eI j)‖) ^ 2
        ≤ (2 * z.im⁻¹) ^ k * (2 * z.im⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * z.im⁻¹) ^ (k + 1 + 1) := by rw [← pow_add]
      _ ≤ ((2 + τ⁻¹) * N) ^ (k + 1 + 1) := pow_le_pow_left₀ (by positivity) h3 _

/-! ## The a priori event -/

/-- The event of Lemma 12.6 at the test vectors `e_a, e_b` and `v, e_b`, together with (ii) at
`v`: `|(G − Π)_{ab}|, |(G − Π)_{vb}| ≤ N^{2ε} N^{2δ}` and `Im G_{vv}/(Nη) ≤ N^{2ε} N^{(C₀+1)δ} Ψ²`
hold with probability `≥ 1 − N^{−(D−4)}` (`N² + N + 1 ≤ N³` events). -/
private lemma highOrder_event {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    {z : ℂ} {ε δ D C₀ Ψ : ℝ} (v : Fin N → ℝ) (hv : testNorm v = 1)
    (h1 : ∀ x y : Fin N → ℝ, DomAt N ε (D - 1)
      (fun ω => ‖testBilin x (GW A (W ω) z - piW A z) y‖)
      (fun _ => (N : ℝ) ^ (2 * δ) * testNorm x * testNorm y))
    (h2 : DomAt N ε D (fun ω => (ent (GW A (W ω) z) v v).im / (N * z.im))
      (fun _ => (N : ℝ) ^ ((C₀ + 1) * δ) * Ψ ^ 2)) :
    HighProbAt N (D - 4) {ω |
      (∀ a b, ‖ent (GW A (W ω) z - piW A z) (eI a) (eI b)‖ ≤
        (N : ℝ) ^ ε * (N : ℝ) ^ (2 * δ)) ∧
      (∀ b, ‖ent (GW A (W ω) z - piW A z) v (eI b)‖ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (2 * δ)) ∧
      (ent (GW A (W ω) z) v v).im / (N * z.im) ≤
        (N : ℝ) ^ ε * ((N : ℝ) ^ ((C₀ + 1) * δ) * Ψ ^ 2)} := by
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set L : Option (Fin N) → Fin N → ℝ := fun o => o.elim v eI with hL
  have hLn : ∀ o, testNorm (L o) = 1 := by
    intro o
    rcases o with _ | a
    · exact hv
    · exact highOrder_testNorm_eI a
  let Ev : (Option (Fin N) × Fin N) ⊕ Unit → Set Ω := Sum.elim
    (fun ob => {ω | ‖testBilin (L ob.1) (GW A (W ω) z - piW A z) (eI ob.2)‖ ≤
      (N : ℝ) ^ ε * ((N : ℝ) ^ (2 * δ) * testNorm (L ob.1) * testNorm (eI ob.2))})
    (fun _ => {ω | (ent (GW A (W ω) z) v v).im / (N * z.im) ≤
        (N : ℝ) ^ ε * ((N : ℝ) ^ ((C₀ + 1) * δ) * Ψ ^ 2)})
  have hdom : ∀ {ξ ζ : Ω → ℝ} {D' : ℝ}, DomAt N ε D' ξ ζ →
      HighProbAt N D' {ω | ξ ω ≤ (N : ℝ) ^ ε * ζ ω} := by
    intro ξ ζ D' h
    unfold HighProbAt
    refine le_trans (measure_mono fun ω hω => ?_) h
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    exact hω
  have hEv : ∀ ι ∈ (Finset.univ : Finset ((Option (Fin N) × Fin N) ⊕ Unit)),
      HighProbAt N (D - 4 + 3) (Ev ι) := by
    intro ι _
    rw [show D - 4 + 3 = D - 1 by ring]
    rcases ι with ⟨o, b⟩ | u
    · exact hdom (h1 (L o) (eI b))
    · have h := hdom h2
      unfold HighProbAt at h ⊢
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hcard : ((Finset.univ : Finset ((Option (Fin N) × Fin N) ⊕ Unit)).card : ℝ) ≤
      (N : ℝ) ^ (3 : ℝ) := by
    rw [Finset.card_univ]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Fintype.card_unit]
    push_cast
    have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h3]
    have h4 : (N : ℝ) * 2 ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left hN2r hNp.le
    have h5 : (N : ℝ) * N * 2 ≤ (N : ℝ) * N * N := mul_le_mul_of_nonneg_left hN2r (by positivity)
    nlinarith
  have hall := HighProbAt.biInter Finset.univ hN1 hcard hEv
  refine (measure_mono (Set.compl_subset_compl.2 fun ω hω => ?_)).trans hall
  have hω' : ∀ ι, ω ∈ Ev ι := fun ι => Set.mem_iInter₂.1 hω ι (Finset.mem_univ _)
  refine ⟨fun a b => ?_, fun b => ?_, hω' (Sum.inr ())⟩
  · have h := hω' (Sum.inl (some a, b))
    simp only [Ev, Sum.elim_inl, Set.mem_ofPred_eq, hLn, highOrder_testNorm_eI, mul_one] at h
    exact h
  · have h := hω' (Sum.inl (none, b))
    simp only [Ev, Sum.elim_inl, Set.mem_ofPred_eq, hLn, highOrder_testNorm_eI, mul_one] at h
    exact h

/-! ## Bounds on `Ψ^W` -/

/-- On `𝐃^W(τ, N)` with `C₀δ ≤ τ/4` and `N^{τ/4} ≥ 2`: `Ψ ≥ τ/N`, `N^{−1/2} ≤ (3τ⁻¹ + 1) Ψ`
(from `Im m^W ≥ (3τ⁻¹ + 1)⁻² η`) and `N^{C₀δ} Ψ ≤ 1`. -/
private lemma highOrder_psi {τ : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hτ : 0 < τ)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hnA : ‖A‖ ≤ τ⁻¹) {z : ℂ}
    (hz : z ∈ domW τ N) {C₀ δ : ℝ} (hC0δ : 0 ≤ C₀ * δ) (hC₀δ : C₀ * δ ≤ τ / 4)
    (h2 : 2 ≤ (N : ℝ) ^ (τ / 4)) :
    0 ≤ PsiW (specOf A) z ∧ τ / N ≤ PsiW (specOf A) z ∧
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (3 * τ⁻¹ + 1) * PsiW (specOf A) z ∧
      (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z ≤ 1 := by
  obtain ⟨hη0, hE, hηl, hηu⟩ := hz
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  set m := mW (specOf A) z with hmdef
  have hm0 : 0 < m.im := (mW_spec hN1 _ hη0).1
  have hm1 : m.im < 1 := (Complex.im_le_norm _).trans_lt (norm_mW_lt_one hN1 _ hη0)
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i => (abs_specOf_le_norm hA i).trans hnA
  have hmge := im_mW_ge hN1 hτ ha hη0 hE hηu
  set X := (N : ℝ) * z.im with hX
  have hX0 : 0 < X := by positivity
  have hsq0 : 0 ≤ √(m.im / X) := Real.sqrt_nonneg _
  have hΨdef : PsiW (specOf A) z = √(m.im / X) + 1 / X := rfl
  have hΨ1 : 1 / X ≤ PsiW (specOf A) z := by rw [hΨdef]; linarith
  have hΨ0 : 0 ≤ PsiW (specOf A) z := le_trans (by positivity) hΨ1
  refine ⟨hΨ0, ?_, ?_, ?_⟩
  · refine le_trans ?_ hΨ1
    rw [div_le_div_iff₀ hNp hX0, one_mul, hX]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  · set k₀ := 3 * τ⁻¹ + 1 with hk₀
    have hk₀0 : 0 < k₀ := by positivity
    have hκ : (k₀ ^ 2)⁻¹ / N ≤ m.im / X := by
      rw [hX, div_le_div_iff₀ hNp hX0]
      calc (k₀ ^ 2)⁻¹ * (N * z.im) = (k₀ ^ 2)⁻¹ * z.im * N := by ring
        _ ≤ m.im * N := mul_le_mul_of_nonneg_right hmge hNp.le
    have h1 : (N : ℝ) ^ (-(1 / 2 : ℝ)) = k₀ * √((k₀ ^ 2)⁻¹ / N) := by
      rw [Real.sqrt_div' _ hNp.le, Real.sqrt_inv, Real.sqrt_sq hk₀0.le, Real.sqrt_eq_rpow,
        Real.rpow_neg hNp.le]
      field_simp
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ hk₀0.le
    exact (Real.sqrt_le_sqrt hκ).trans (by rw [hΨdef]; linarith [hΨ1, show 0 ≤ 1 / X by positivity])
  · set u := (N : ℝ) ^ (τ / 4) with hu
    have hu0 : 0 < u := by positivity
    have hu4 : u ^ 4 ≤ X := by
      calc u ^ 4 = (N : ℝ) ^ τ := by
            rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num
        _ = N * (N : ℝ) ^ (-1 + τ) := by
            rw [Real.rpow_add hNp, Real.rpow_neg_one]; field_simp
        _ ≤ N * z.im := mul_le_mul_of_nonneg_left hηl hNp.le
    set g := (N : ℝ) ^ (C₀ * δ) with hg
    have hg1 : 1 ≤ g := Real.one_le_rpow hN1r hC0δ
    have hgu : g ≤ u := Real.rpow_le_rpow_of_exponent_le hN1r hC₀δ
    have hX' : u ^ 4 ≤ X := hu4
    have ht1 : g * √(m.im / X) ≤ 1 / 2 := by
      have hgs : g * √(m.im / X) = √(g ^ 2 * m.im / X) := by
        rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
      rw [hgs]
      have hle : g ^ 2 * m.im / X ≤ (1 / u) ^ 2 := by
        rw [div_le_iff₀ hX0, div_pow, one_pow]
        have h3 : g ^ 2 * m.im ≤ u ^ 2 := by
          have := pow_le_pow_left₀ (by linarith) hgu 2
          nlinarith
        calc g ^ 2 * m.im ≤ u ^ 2 := h3
          _ = 1 / u ^ 2 * u ^ 4 := by field_simp
          _ ≤ 1 / u ^ 2 * X := by gcongr
      refine (Real.sqrt_le_sqrt hle).trans ?_
      rw [Real.sqrt_sq (by positivity)]
      rw [div_le_div_iff₀ hu0 (by norm_num)]
      linarith
    have ht2 : g * (1 / X) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ hX0 (by norm_num)]
      have h4 : u ^ 4 ≥ 2 * u := by nlinarith [pow_le_pow_left₀ (by norm_num) h2 3]
      nlinarith
    rw [hΨdef, mul_add]
    linarith

/-- `K ≤ N^a` once `N ≥ ⌈K^{1/a}⌉`. -/
private lemma highOrder_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

/-- `3 (10p + 6) ≤ D_prev(p) − 4 = 100 (p + 1)² − 4` for `p ≥ 2`. -/
private lemma highOrder_dPrev_ge {p : ℕ} (hp : 2 ≤ p) :
    3 * (((2 * (5 * p + 3) : ℕ) : ℝ)) ≤ dPrev p - 4 := by
  rw [dPrev]
  push_cast
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- The integration step: if `0 ≤ Z ≤ N^k` everywhere, `Z ≤ T (F + b)` on an event of
probability `≥ 1 − N^{−D}` with `3 (2k) ≤ D`, `N^{−2k} ≤ T b`, and `0 ≤ F` is bounded, then
`E Z ≤ 2 T (b + E F)`. -/
private lemma highOrder_integral {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N k : ℕ} (hN1 : 1 ≤ N) {T b D Fmax : ℝ}
    (hT : 0 ≤ T) (hb : 0 ≤ b) {Z F : Ω → ℝ} (hZm : Measurable Z) (hFm : Measurable F)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hF0 : ∀ ω, 0 ≤ F ω) (hFbd : ∀ ω, F ω ≤ Fmax)
    (hZle : ∀ ω, Z ω ≤ (N : ℝ) ^ k) {Θ : Set Ω} (hZΘ : ∀ ω ∈ Θ, Z ω ≤ T * (F ω + b))
    (hΘ : HighProbAt N D Θ) (hΓ : ((N : ℝ) ^ (2 * k))⁻¹ ≤ T * b)
    (hD : 3 * ((2 * k : ℕ) : ℝ) ≤ D) :
    ∫ ω, Z ω ≤ 2 * T * (b + ∫ ω, F ω) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  set Zmax : ℝ := (N : ℝ) ^ k with hZmax
  have hFint : Integrable F :=
    (integrable_const Fmax).mono' hFm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hF0 ω)]; exact hFbd ω)
  have hZint : Integrable Z :=
    (integrable_const Zmax).mono' hZm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hZ0 ω)]; exact hZle ω)
  set ξ : Ω → ℝ := fun ω => max (Z ω - T * F ω) 0 with hξ
  have hξ0 : ∀ ω, 0 ≤ ξ ω := fun ω => le_max_right _ _
  have hξZ : ∀ ω, ξ ω ≤ Zmax := fun ω =>
    max_le (by
      have h1 := hZle ω
      have h2 := mul_nonneg hT (hF0 ω)
      linarith) (le_trans (hZ0 ω) (hZle ω))
  have hξm : Measurable ξ := (hZm.sub (hFm.const_mul _)).max measurable_const
  have hξint : Integrable ξ :=
    (integrable_const Zmax).mono' hξm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hξ0 ω)]; exact hξZ ω)
  have hξ2int : Integrable fun ω => ξ ω ^ 2 :=
    (integrable_const (Zmax ^ 2)).mono' (hξm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hξ0 ω) (hξZ ω) 2)
  set Cc : ℝ := ((2 * k : ℕ) : ℝ) with hCc
  have hξ2le : ∫ ω, ξ ω ^ 2 ≤ (N : ℝ) ^ Cc := by
    calc ∫ ω, ξ ω ^ 2 ≤ ∫ _ω, Zmax ^ 2 :=
          integral_mono hξ2int (integrable_const _) fun ω => pow_le_pow_left₀ (hξ0 ω) (hξZ ω) 2
      _ = Zmax ^ 2 := by simp
      _ = (N : ℝ) ^ Cc := by rw [hZmax, hCc, Real.rpow_natCast, ← pow_mul, mul_comm]
  have hΓ' : (N : ℝ) ^ (-Cc) ≤ T * b := by
    rw [Real.rpow_neg hNp.le, hCc, Real.rpow_natCast]; exact hΓ
  have hdom : DomAt N 0 D ξ (fun _ => T * b) := by
    unfold DomAt
    refine le_trans (measure_mono fun ω hω => ?_) hΘ
    simp only [Set.mem_ofPred_eq, Real.rpow_zero, one_mul] at hω
    intro hωΘ
    have h1 := hZΘ ω hωΘ
    have h2 : ξ ω ≤ T * b := max_le (by linarith) (mul_nonneg hT hb)
    exact absurd h2 (not_le.2 hω)
  have hint := integral_le_of_domAt hN1 le_rfl hD hΓ' hξ0 hξ2int hξ2le hdom
  rw [Real.rpow_zero, mul_one] at hint
  have hZle' : ∫ ω, Z ω ≤ ∫ ω, (T * F ω + ξ ω) :=
    integral_mono hZint ((hFint.const_mul T).add hξint) fun ω => by
      have := le_max_left (Z ω - T * F ω) 0
      simp only [hξ] at this ⊢
      linarith
  have hEF : 0 ≤ ∫ ω, F ω := integral_nonneg hF0
  have h1 := mul_nonneg hT hEF
  have h2 : ∫ ω, (T * F ω + ξ ω) = (T * ∫ ω, F ω) + ∫ ω, ξ ω := by
    rw [integral_add (hFint.const_mul T) hξint, integral_const_mul]
  rw [h2] at hZle'
  set I := ∫ ω, F ω with hI
  set J := ∫ ω, ξ ω with hJ
  calc ∫ ω, Z ω ≤ T * I + J := hZle'
    _ ≤ 2 * T * (b + I) := by linarith

/-! ## Lemma 12.7 for `n ≥ 4` -/

/-- Lemma 12.7 for `n ∈ [4, 4p]` (lowz), coefficient form: `f^{(n)} = n! fCoeff`. -/
theorem wig_coeff_high (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (P : ModelClassW N) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N C P A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
        ∀ n ∈ Finset.Icc 4 (4 * p), (N : ℝ) ^ (-(n : ℝ) / 2) *
          ∑ α : UpperIdx N, ∫ ω, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ ≤
            K * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p + ∫ ω, FvW A (W ω) z v ^ p) := by
  obtain ⟨N₁, h₁⟩ := wig_rough_bound τ C C₀ δ (δ / 4) (dPrev p) hτ hτ1 hδ hC₀ hC₀δ
    (by positivity)
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hp0 : 0 < p := by omega
  set k₀ : ℝ := 3 * τ⁻¹ + 1 with hk₀
  set Q : ℝ := 1 + τ⁻¹ with hQ
  set K₁ : ℝ := 4 * (k₀ + 1) ^ (4 * p) * (2 * Q) ^ (16 * p) with hK₁
  set T : ℝ := (((4 * p : ℕ) : ℝ) + 1) ^ p with hT
  set K₂ : ℝ := T * (2 + τ⁻¹) ^ (5 * p) with hK₂
  have hk₀0 : 0 ≤ k₀ := by positivity
  have hQ1 : 1 ≤ Q := by linarith
  have hT1 : 1 ≤ T := one_le_pow₀ (by
    have : (0 : ℝ) ≤ ((4 * p : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith)
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨2 * T, by positivity, max (max (max N₁ 2) (max ⌈K₁ ^ δ⁻¹⌉₊ ⌈(2 : ℝ) ^ (τ / 4)⁻¹⌉₊))
    (max ⌈K₂⌉₊ ⌈τ⁻¹ ^ p⌉₊), ?_⟩
  intro N hN A S P m hset hm hA Ω _ _ W hW hP z hz v hv n hn
  have hNN₁ : N₁ ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNK₁ : ⌈K₁ ^ δ⁻¹⌉₊ ≤ N := by omega
  have hN2τ : ⌈(2 : ℝ) ^ (τ / 4)⁻¹⌉₊ ≤ N := by omega
  have hNK₂ : ⌈K₂⌉₊ ≤ N := by omega
  have hNτ : ⌈τ⁻¹ ^ p⌉₊ ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hn' := Finset.mem_Icc.1 hn
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have hη : 0 < z.im := hzD.1
  have hηN : z.im⁻¹ ≤ N := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have h2 : (N : ℝ)⁻¹ ≤ z.im := by rw [← Real.rpow_neg_one]; exact h1.trans hzD.2.2.1
    calc z.im⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) h2
      _ = N := inv_inv _
  have hAh := hset.symmA
  have h2u : 2 ≤ (N : ℝ) ^ (τ / 4) :=
    highOrder_le_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 < τ / 4) hN2τ
  have hC0δ : 0 ≤ C₀ * δ := mul_nonneg (by linarith) hδ.le
  obtain ⟨hΨ0, hΨτ, hsi, hgΨ⟩ := highOrder_psi hN1 hτ hAh hset.normA hzD hC0δ hC₀δ h2u
  set Ψ := PsiW (specOf A) z with hΨdef
  set g := (N : ℝ) ^ (C₀ * δ) with hg
  set d := (N : ℝ) ^ δ with hd
  set e := (N : ℝ) ^ (δ / 4) with he
  set s := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hs
  have hd1 : 1 ≤ d := Real.one_le_rpow hN1r hδ.le
  have he1 : 1 ≤ e := Real.one_le_rpow hN1r (by positivity)
  have he4 : e ^ 4 ≤ d := by
    rw [he, hd, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num
  have hg30 : d ^ 30 ≤ g := by
    rw [hd, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by push_cast; nlinarith)
  have hg0 : 0 ≤ g := Real.rpow_nonneg hNp.le _
  have hgd : (N : ℝ) ^ ((C₀ + 1) * δ) = g * d := by
    rw [hg, hd, ← Real.rpow_add hNp]; ring_nf
  have he2 : (N : ℝ) ^ (2 * (δ / 4)) = e ^ 2 := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  have hd2 : (N : ℝ) ^ (2 * δ) = d ^ 2 := by
    rw [hd, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  have hs0 : 0 ≤ s := Real.rpow_nonneg hNp.le _
  have hs1 : s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
  have hsN : s ^ 4 * (N : ℝ) ^ 2 = 1 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_natCast (N : ℝ) 2,
      ← Real.rpow_add hNp]
    norm_num
  have hsn : (N : ℝ) ^ (-(n : ℝ) / 2) = s ^ n := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  have hK₁d : K₁ ≤ d := highOrder_le_rpow hK₁0 hδ hNK₁
  have hK : 4 * k₀ ^ (n - 4) * (2 * Q) ^ (4 * n) ≤ d := by
    refine le_trans ?_ hK₁d
    have ha : k₀ ^ (n - 4) ≤ (k₀ + 1) ^ (4 * p) :=
      (pow_le_pow_left₀ hk₀0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
    have hb : (2 * Q) ^ (4 * n) ≤ (2 * Q) ^ (16 * p) := pow_le_pow_right₀ (by linarith) (by omega)
    calc 4 * k₀ ^ (n - 4) * (2 * Q) ^ (4 * n) ≤ 4 * (k₀ + 1) ^ (4 * p) * (2 * Q) ^ (16 * p) := by
          gcongr
      _ = K₁ := rfl
  -- the a priori event
  have hrb := h₁ N hNN₁ A S P m hset hm hA Ω W hW hP z hz
  have hΘ := highOrder_event hN2 (A := A) (W := W) v hv hrb.1 (hrb.2 v hv)
  set Θ := {ω |
      (∀ a b, ‖ent (GW A (W ω) z - piW A z) (eI a) (eI b)‖ ≤
        (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ)) ∧
      (∀ b, ‖ent (GW A (W ω) z - piW A z) v (eI b)‖ ≤
        (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ)) ∧
      (ent (GW A (W ω) z) v v).im / (N * z.im) ≤
        (N : ℝ) ^ (2 * (δ / 4)) * ((N : ℝ) ^ ((C₀ + 1) * δ) * Ψ ^ 2)} with hΘdef
  have hPi : ∀ x y : Fin N → ℝ, testNorm x = 1 → testNorm y = 1 →
      ‖ent (piW A z) x y‖ ≤ τ⁻¹ := by
    intro x y hx hy
    have := norm_piW_le hτ hAh hset.standing hzS x y
    rw [hx, hy, mul_one, mul_one] at this
    exact this
  have hE1 : 1 ≤ e ^ 2 * d ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ he1)
    (one_le_pow₀ hd1)
  have hentB : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ), testNorm x = 1 →
      testNorm y = 1 → ‖ent (M - piW A z) x y‖ ≤ e ^ 2 * d ^ 2 →
      ‖ent M x y‖ ≤ e ^ 2 * d ^ 2 * Q := by
    intro M x y hx hy hM
    have h1 : ent M x y = ent (M - piW A z) x y + ent (piW A z) x y := by
      rw [highOrder_ent_sub]; ring
    rw [h1, hQ]
    calc ‖ent (M - piW A z) x y + ent (piW A z) x y‖
        ≤ ‖ent (M - piW A z) x y‖ + ‖ent (piW A z) x y‖ := norm_add_le _ _
      _ ≤ e ^ 2 * d ^ 2 + τ⁻¹ := add_le_add hM (hPi x y hx hy)
      _ ≤ e ^ 2 * d ^ 2 * (1 + τ⁻¹) := by
          rw [mul_add, mul_one]
          linarith [mul_le_mul_of_nonneg_right hE1 hτi.le]
  have hon : ∀ ω ∈ Θ, (∀ a b, ‖ent (GW A (W ω) z) (eI a) (eI b)‖ ≤ e ^ 2 * d ^ 2 * Q) ∧
      (∀ c, ‖ent (GW A (W ω) z) v (eI c)‖ ≤ e ^ 2 * d ^ 2 * Q) ∧
      ∑ s, ‖ent (GW A (W ω) z) v (eI s)‖ ^ 2 ≤ N * (e ^ 2 * (g * d) * Ψ ^ 2) := by
    intro ω hω
    obtain ⟨h1, h2, h3⟩ := hω
    rw [he2, hd2] at h1 h2
    rw [he2, hgd] at h3
    refine ⟨fun a b => hentB _ _ _ (highOrder_testNorm_eI a) (highOrder_testNorm_eI b) (h1 a b),
      fun c => hentB _ _ _ hv (highOrder_testNorm_eI c) (h2 c), ?_⟩
    rw [highOrder_ward hAh (hW.symm ω) hη]
    have hNη : 0 < (N : ℝ) * z.im := by positivity
    have : (ent (GW A (W ω) z) v v).im / z.im =
        N * ((ent (GW A (W ω) z) v v).im / (N * z.im)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (le_of_le_of_eq h3 (by ring)) hNp.le
  -- the random variables
  set Z : Ω → ℝ := fun ω => s ^ n *
    ∑ α : UpperIdx N, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ with hZ
  set Fp : Ω → ℝ := fun ω => FvW A (W ω) z v ^ p with hFp
  set b := (g * Ψ) ^ p with hb
  have hb0 : 0 ≤ b := pow_nonneg (mul_nonneg hg0 hΨ0) p
  set Tset := Finset.Nat.antidiagonalTuple p n with hTset
  have hTcard : (Tset.card : ℝ) ≤ T := by
    refine (highOrder_card_tuple p n).trans (pow_le_pow_left₀ (by positivity) ?_ p)
    have : (n : ℝ) ≤ ((4 * p : ℕ) : ℝ) := by exact_mod_cast hn'.2
    linarith
  have hZΘ : ∀ ω ∈ Θ, Z ω ≤ T * (Fp ω + b) := by
    intro ω hω
    obtain ⟨hGab, hR, hWb⟩ := hon ω hω
    have hF0 : 0 ≤ Fp ω := pow_nonneg (norm_nonneg _) p
    have hper : ∀ κ ∈ Tset, s ^ n * ∑ α : UpperIdx N,
        ∏ r, ‖resCoeffW A (W ω) z v α.1.1 α.1.2 (κ r)‖ ≤ Fp ω + b := fun κ hκ =>
      highOrder_event_tuple hAh (hW.symm ω) hη v hp0 hn'.1 κ
        (Finset.Nat.mem_antidiagonalTuple.1 hκ) hs0 hsN hΨ0 hd1 he1 he4 hg30 hgΨ hsi hk₀0 hQ1
        hK hGab hR hWb
    calc Z ω ≤ s ^ n * ∑ α : UpperIdx N, ∑ κ ∈ Tset,
          ∏ r, ‖resCoeffW A (W ω) z v α.1.1 α.1.2 (κ r)‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ =>
            highOrder_norm_fCoeff_le p n _) (pow_nonneg hs0 n)
      _ = ∑ κ ∈ Tset, s ^ n * ∑ α : UpperIdx N,
          ∏ r, ‖resCoeffW A (W ω) z v α.1.1 α.1.2 (κ r)‖ := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ _κ ∈ Tset, (Fp ω + b) := Finset.sum_le_sum hper
      _ = (Tset.card : ℝ) * (Fp ω + b) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T * (Fp ω + b) := mul_le_mul_of_nonneg_right hTcard (by positivity)
  -- deterministic bounds
  have hcoef : ∀ ω (α : UpperIdx N), ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ ≤
      K₂ * (N : ℝ) ^ (5 * p) := by
    intro ω α
    refine (highOrder_det_bound hAh (hW.symm ω) hη hηN hN1 hτ hv (hPi v v hv hv) _ _ p n).trans ?_
    have h1 : ((n : ℝ) + 1) ^ p ≤ T := by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      have : (n : ℝ) ≤ ((4 * p : ℕ) : ℝ) := by exact_mod_cast hn'.2
      linarith
    have hL1 : 1 ≤ (2 + τ⁻¹) * N := one_le_mul_of_one_le_of_one_le (by linarith) hN1r
    have h2 : ((2 + τ⁻¹) * N) ^ (n + p) ≤ ((2 + τ⁻¹) * N) ^ (5 * p) :=
      pow_le_pow_right₀ hL1 (by omega)
    calc ((n : ℝ) + 1) ^ p * ((2 + τ⁻¹) * N) ^ (n + p) ≤ T * ((2 + τ⁻¹) * N) ^ (5 * p) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = K₂ * (N : ℝ) ^ (5 * p) := by rw [hK₂, mul_pow]; ring
  have hK₂N : K₂ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK₂)
  set Zmax : ℝ := (N : ℝ) ^ (5 * p + 3) with hZmax
  have hZle : ∀ ω, Z ω ≤ Zmax := by
    intro ω
    have hsum : ∑ α : UpperIdx N, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ ≤
        (N : ℝ) ^ 2 * (K₂ * (N : ℝ) ^ (5 * p)) := by
      calc ∑ α : UpperIdx N, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖
          ≤ ∑ α : UpperIdx N, K₂ * (N : ℝ) ^ (5 * p) := Finset.sum_le_sum fun α _ => hcoef ω α
        _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, K₂ * (N : ℝ) ^ (5 * p) :=
            highOrder_sum_upper_le (fun _ _ => K₂ * (N : ℝ) ^ (5 * p)) fun _ _ => by positivity
        _ = (N : ℝ) ^ 2 * (K₂ * (N : ℝ) ^ (5 * p)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hsn1 : s ^ n ≤ 1 := pow_le_one₀ hs0 hs1
    calc Z ω ≤ 1 * ((N : ℝ) ^ 2 * (K₂ * (N : ℝ) ^ (5 * p))) :=
          mul_le_mul hsn1 hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ ≤ (N : ℝ) ^ 2 * (N * (N : ℝ) ^ (5 * p)) := by
          rw [one_mul]; gcongr
      _ = Zmax := by rw [hZmax]; ring
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  have hcm : ∀ α : UpperIdx N,
      Measurable fun ω => ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ := fun α =>
    highOrder_measurable_coeff hWm A z v α.1.1 α.1.2 p n
  have hcint : ∀ α : UpperIdx N,
      Integrable fun ω => ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ := fun α =>
    (integrable_const (K₂ * (N : ℝ) ^ (5 * p))).mono' (hcm α).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hcoef ω α)
  have hZm : Measurable Z :=
    (Finset.measurable_sum _ fun α _ => hcm α).const_mul _
  have hFm : Measurable Fp := (highOrder_measurable_Fv hWm A z v).pow_const p
  have hFbd : ∀ ω, Fp ω ≤ ((N : ℝ) + τ⁻¹) ^ p := by
    intro ω
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ p
    change ‖ent (GW A (W ω) z - piW A z) v v‖ ≤ _
    rw [highOrder_ent_sub]
    have h1 := highOrder_norm_ent_le hAh (hW.symm ω) hη v v
    rw [hv, mul_one, mul_one] at h1
    exact (norm_sub_le _ _).trans (add_le_add (h1.trans hηN) (hPi v v hv hv))
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω =>
    mul_nonneg (pow_nonneg hs0 n) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hΓ : ((N : ℝ) ^ (2 * (5 * p + 3)))⁻¹ ≤ T * b := by
    have hτN : τ⁻¹ ^ p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
    have h1 : (N : ℝ) ^ (p + 1) ≤ (N : ℝ) ^ (2 * (5 * p + 3)) :=
      pow_le_pow_right₀ hN1r (by omega)
    have h2 : (τ / N) ^ p ≤ Ψ ^ p := pow_le_pow_left₀ (by positivity) hΨτ p
    have hg1 : 1 ≤ g := Real.one_le_rpow hN1r hC0δ
    have h3 : Ψ ^ p ≤ b := pow_le_pow_left₀ hΨ0 (le_mul_of_one_le_left hΨ0 hg1) p
    have h5 : (N : ℝ)⁻¹ ≤ τ ^ p := by
      have := inv_anti₀ (by positivity : (0 : ℝ) < τ⁻¹ ^ p) hτN
      rwa [inv_pow, inv_inv] at this
    have h4 : ((N : ℝ) ^ (p + 1))⁻¹ ≤ (τ / N) ^ p :=
      calc ((N : ℝ) ^ (p + 1))⁻¹ = (N : ℝ)⁻¹ * ((N : ℝ) ^ p)⁻¹ := by
            rw [pow_succ, mul_inv, mul_comm]
        _ ≤ τ ^ p * ((N : ℝ) ^ p)⁻¹ := mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = (τ / N) ^ p := by rw [div_pow, div_eq_mul_inv]
    calc ((N : ℝ) ^ (2 * (5 * p + 3)))⁻¹ ≤ ((N : ℝ) ^ (p + 1))⁻¹ := inv_anti₀ (by positivity) h1
      _ ≤ b := h4.trans (h2.trans h3)
      _ ≤ T * b := le_mul_of_one_le_left hb0 hT1
  have hLHS : (N : ℝ) ^ (-(n : ℝ) / 2) *
      ∑ α : UpperIdx N, ∫ ω, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖ = ∫ ω, Z ω := by
    rw [hZ, integral_const_mul, integral_finsetSum _ fun α _ => hcint α, hsn]
  rw [hLHS]
  exact highOrder_integral hN1 (le_trans zero_le_one hT1) hb0 hZm hFm hZ0
    (fun ω => pow_nonneg (norm_nonneg _) p) hFbd hZle hZΘ hΘ hΓ (highOrder_dPrev_ge hp2)

#print axioms wig_coeff_high

end Anisotropic
