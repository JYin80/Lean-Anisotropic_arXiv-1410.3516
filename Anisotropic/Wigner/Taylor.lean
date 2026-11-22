module

public import Anisotropic.Comparison.Ladder
public import Anisotropic.Comparison.MainII
public import Anisotropic.Comparison.Props
public import Anisotropic.Comparison.Words
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Interp
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

/-! # Moment matching against the GOE and the step from 0 to θ -/

/-! ## The spectral form of `G^W` and invertibility -/

/-- A real symmetric `M` is `U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma taylor_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
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

/-- For `M = U diag(λ) Uᵀ` with `U` real orthogonal and `λₖ − w ≠ 0`, the rotated diagonal
`(λₖ − w)⁻¹` is a right inverse of `M − w`. -/
private lemma taylor_right_inv {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
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

/-- `M − z` is invertible for a real symmetric `M` and `Im z > 0`. -/
private lemma taylor_isUnit_det {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : IsUnit (cplx M - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  obtain ⟨U, l, hUU, hUU', hMU⟩ := taylor_eig_decomp hM
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  exact Matrix.isUnit_det_of_right_inverse (taylor_right_inv hUU hUU' hMU hne)

/-! ## Updates of a symmetric matrix -/

/-- The update of a symmetric matrix is symmetric. -/
private lemma taylor_Wupd_symm {N : ℕ} {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
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
private lemma taylor_Wupd_self {N : ℕ} {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
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
private lemma taylor_herm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) (i j : Fin N) (t : ℝ) : (Wupd Wm i j t + A).IsHermitian := by
  have hW' : (Wupd Wm i j t).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact taylor_Wupd_symm hW i j t
  exact hW'.add hA

/-- `H(y) − H(x) = (y − x) Δ` for `H(t) = W^{(ij),t} + A − z`. -/
private lemma taylor_H_sub {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N)
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
private lemma taylor_res_id {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x y : ℝ) :
    GW A (Wupd Wm i j y) z - GW A (Wupd Wm i j x) z =
      (-((y - x : ℝ) : ℂ)) • (GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j y) z) := by
  set Hx := cplx (Wupd Wm i j x + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hHx
  set Hy := cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hHy
  have hx : IsUnit Hx.det := taylor_isUnit_det (taylor_herm hA hW i j x) hz
  have hy : IsUnit Hy.det := taylor_isUnit_det (taylor_herm hA hW i j y) hz
  have e1 : Hx⁻¹ * Hx = 1 := Matrix.nonsing_inv_mul _ hx
  have e2 : Hy * Hy⁻¹ = 1 := Matrix.mul_nonsing_inv _ hy
  have hs := taylor_H_sub A Wm z i j x y
  change Hy⁻¹ - Hx⁻¹ = (-((y - x : ℝ) : ℂ)) • (Hx⁻¹ * deltaW i j * Hy⁻¹)
  have key : Hx⁻¹ * (Hx - Hy) * Hy⁻¹ = Hy⁻¹ - Hx⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [← key, show Hx - Hy = -(Hy - Hx) by abel, hs, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, neg_smul]

/-! ## Derivatives along the entry `(i, j)` -/

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def TaylorMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private lemma taylor_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : TaylorMD f f' x) (hg : TaylorMD g g' x) :
    TaylorMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private lemma taylor_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    TaylorMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

private lemma taylor_ent_eq {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private lemma taylor_MD_ent {ι : Type*} [Fintype ι] {f : ℝ → Matrix ι ι ℂ}
    {f' : Matrix ι ι ℂ} {x : ℝ} (hf : TaylorMD f f' x) (a b : ι → ℝ) :
    HasDerivAt (fun y => ent (f y) a b) (ent f' a b) x := by
  simp only [taylor_ent_eq]
  exact HasDerivAt.fun_sum fun s _ => HasDerivAt.fun_sum fun t _ =>
    ((hf s t).const_mul _).mul_const _

/-- `y ↦ G(W^{(ij),y})` is continuous. -/
private lemma taylor_continuousAt_G {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
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
  have hu := taylor_isUnit_det (taylor_herm hA hW i j x) hz
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  exact hinv.comp (f := fun y => cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))
    hX.continuousAt

/-- `d/dy G(W^{(ij),y}) = −G Δ G`. -/
private lemma taylor_MD_G {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) :
    TaylorMD (fun y => GW A (Wupd Wm i j y) z)
      (-(GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j x) z)) x := by
  intro s t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set G0 := GW A (Wupd Wm i j x) z with hG0
  have hid : ∀ h : ℝ, GW A (Wupd Wm i j (x + h)) z - G0 =
      (-(h : ℂ)) • (G0 * deltaW i j * GW A (Wupd Wm i j (x + h)) z) := by
    intro h
    have e := taylor_res_id hA hW hz i j x (x + h)
    rw [show x + h - x = h by ring] at e
    exact e
  have hc : ∀ r, ContinuousAt (fun h : ℝ => GW A (Wupd Wm i j (x + h)) z r t) 0 := fun r => by
    have h2 : ContinuousAt (fun h : ℝ => x + h) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have h3 : ContinuousAt ((fun y => GW A (Wupd Wm i j y) z) ∘ fun h : ℝ => x + h) 0 :=
      ContinuousAt.comp_of_eq (taylor_continuousAt_G hA hW hz i j x) h2 (by simp)
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
private lemma taylor_MD_pow {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    TaylorMD (fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-(k : ℂ) • (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using taylor_MD_const (1 : Matrix (Fin N) (Fin N) ℂ) x
  | succ k ih =>
    have hDG := taylor_MD_mul (taylor_MD_const (deltaW i j) x) (taylor_MD_G hA hW hz i j x)
    have h := taylor_MD_mul ih hDG
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
private lemma taylor_MD_T {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    TaylorMD (fun y => GW A (Wupd Wm i j y) z * (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-((k : ℂ) + 1) • (GW A (Wupd Wm i j x) z *
        (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1))) x := by
  have h := taylor_MD_mul (taylor_MD_G hA hW hz i j x) (taylor_MD_pow hA hW hz i j x k)
  convert h using 1
  rw [Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_assoc (GW A (Wupd Wm i j x) z) (deltaW i j),
    Matrix.mul_assoc (GW A (Wupd Wm i j x) z), ← pow_succ', neg_add, add_smul, neg_one_smul,
    add_comm]

/-- `d/dx a_k(x) = (k + 1) a_{k+1}(x)` along the entry `(i, j)` of a symmetric matrix. -/
private lemma taylor_hasDerivAt_resCoeffW {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i j : Fin N)
    (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => resCoeffW A (Wupd Wm i j y) z v i j k)
      (((k : ℂ) + 1) * resCoeffW A (Wupd Wm i j x) z v i j (k + 1)) x := by
  have hT := taylor_MD_T hA hW hz i j x k
  have hC : TaylorMD (fun y => GW A (Wupd Wm i j y) z * (deltaW i j * GW A (Wupd Wm i j y) z) ^ k
      - if k = 0 then piW A z else 0)
      (-((k : ℂ) + 1) • (GW A (Wupd Wm i j x) z *
        (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1))) x := by
    intro s t
    simpa using (hT s t).sub_const ((if k = 0 then piW A z else 0) s t)
  have h := (taylor_MD_ent hC v v).const_mul ((-1 : ℂ) ^ k)
  refine h.congr_deriv ?_
  have hs : ∀ (c : ℂ) (B : Matrix (Fin N) (Fin N) ℂ), ent (c • B) v v = c * ent B v v := by
    intro c B
    simp [ent, smul_mulVec, dotProduct_smul]
  simp only [resCoeffW, hs, Nat.succ_ne_zero, ↓reduceIte, sub_zero, pow_succ]
  ring

/-! ## Measurability -/

/-- `W ↦ G^W(z)` is measurable. -/
private lemma taylor_measurable_G {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
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

/-- `B ↦ ⟨x, B y⟩` is continuous. -/
private lemma taylor_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => taylor_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

/-- `W ↦ a_k(W)` is measurable. -/
private lemma taylor_measurable_res {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (k : ℕ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => resCoeffW A Wm z v i j k := by
  have hc : Continuous fun X : Matrix (Fin N) (Fin N) ℂ =>
      (-1 : ℂ) ^ k * ent (X * (deltaW i j * X) ^ k - if k = 0 then piW A z else 0) v v :=
    continuous_const.mul ((taylor_continuous_ent v v).comp
      ((continuous_id.matrix_mul ((continuous_const.matrix_mul continuous_id).pow k)).sub
        continuous_const))
  exact hc.measurable.comp (taylor_measurable_G A z)

/-- `x ↦ f_n(a(x))` is measurable when every `x ↦ a_k(x)` is. -/
private lemma taylor_measurable_fCoeff {X : Type*} [MeasurableSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Measurable fun x => a x k) :
    Measurable fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine Finset.measurable_sum _ fun κ _ => Finset.measurable_prod _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.measurable.comp (ha _)

/-- `(W, t) ↦ W^{(ij),t}` is continuous. -/
private lemma taylor_continuous_Wupd {N : ℕ} (i j : Fin N) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => Wupd q.1 i j q.2 := by
  refine continuous_pi fun s => continuous_pi fun u => ?_
  simp only [Wupd]
  split_ifs
  · exact continuous_snd
  · exact continuous_fst.matrix_elem s u

/-- `W ↦ f_n(a(W^{(ij),t}))` is measurable. -/
private lemma taylor_measurable_fUpd {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (p n : ℕ) (t : ℝ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      fCoeff p (resCoeffW A (Wupd Wm i j t) z v i j) n :=
  taylor_measurable_fCoeff p n fun k => (taylor_measurable_res A z v i j k).comp
    ((taylor_continuous_Wupd i j).measurable.comp (measurable_id.prodMk measurable_const))

/-! ## Deterministic bounds on the coefficients -/

/-- The elementary matrix `E_{ab}`. -/
private def taylorE {N : ℕ} (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun s u => if s = a ∧ u = b then 1 else 0

private lemma taylor_ent_add {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X + Y) x y = ent X x y + ent Y x y := by
  simp [ent, add_mulVec, dotProduct_add]

private lemma taylor_ent_sub {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X - Y) x y = ent X x y - ent Y x y := by
  simp [ent, Matrix.sub_mulVec, dotProduct_sub]

private lemma taylor_ent_smul {N : ℕ} (c : ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (c • X) x y = c * ent X x y := by
  simp [ent, smul_mulVec, dotProduct_smul]

/-- `⟨x, X E_{ab} Y y⟩ = ⟨x, X e_a⟩ ⟨e_b, Y y⟩`. -/
private lemma taylor_ent_single {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N)
    (x y : Fin N → ℝ) : ent (X * taylorE a b * Y) x y = ent X x (eI a) * ent Y (eI b) y := by
  have h1 : ∀ s u, (X * taylorE a b) s u = if u = b then X s a else 0 := by
    intro s u
    simp only [Matrix.mul_apply, taylorE, Matrix.of_apply]
    by_cases hu : u = b
    · subst hu
      simp
    · simp [hu]
  have h2 : X * taylorE a b * Y = fun s t => X s a * Y b t := by
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

private lemma taylor_deltaW_ne {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    deltaW i j = taylorE i j + taylorE j i := by
  ext s u
  simp only [deltaW, taylorE, Matrix.add_apply, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all

private lemma taylor_deltaW_eq {N : ℕ} (i : Fin N) : deltaW i i = taylorE i i := by
  ext s u
  simp [deltaW, taylorE]

/-- `|⟨x, X Δ Y y⟩| ≤ |⟨x, X e_i⟩||⟨e_j, Y y⟩| + |⟨x, X e_j⟩||⟨e_i, Y y⟩|`. -/
private lemma taylor_ent_delta_le {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (x y : Fin N → ℝ) :
    ‖ent (X * deltaW i j * Y) x y‖ ≤ ‖ent X x (eI i)‖ * ‖ent Y (eI j) y‖ +
      ‖ent X x (eI j)‖ * ‖ent Y (eI i) y‖ := by
  by_cases h : i = j
  · subst h
    rw [taylor_deltaW_eq, taylor_ent_single, norm_mul]
    exact le_add_of_nonneg_right (by positivity)
  · rw [taylor_deltaW_ne h, Matrix.mul_add, Matrix.add_mul, taylor_ent_add, taylor_ent_single,
      taylor_ent_single]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]

/-- The word bound: if `|G_{xy}| ≤ b` for `x, y ∈ {u₀, e_i, e_j}`, then
`|(G (Δ G)^k)_{xy}| ≤ (2b)^k b`. -/
private lemma taylor_word_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (u : Fin 3 → Fin N → ℝ) (hu1 : u 1 = eI i) (hu2 : u 2 = eI j) {b : ℝ}
    (hb : ∀ a c, ‖ent G (u a) (u c)‖ ≤ b) :
    ∀ k a c, ‖ent (G * (deltaW i j * G) ^ k) (u a) (u c)‖ ≤ (2 * b) ^ k * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  intro k
  induction k with
  | zero =>
    intro a c
    simpa using hb a c
  | succ k ih =>
    intro a c
    have e : G * (deltaW i j * G) ^ (k + 1) = G * (deltaW i j * G) ^ k * deltaW i j * G := by
      rw [pow_succ]
      simp only [Matrix.mul_assoc]
    rw [e]
    refine (taylor_ent_delta_le _ _ i j _ _).trans ?_
    have h1 := ih a 1
    have h2 := ih a 2
    have g1 := hb 2 c
    have g2 := hb 1 c
    rw [hu1] at h1 g2
    rw [hu2] at h2 g1
    have hk : 0 ≤ (2 * b) ^ k * b := by positivity
    calc _ ≤ (2 * b) ^ k * b * b + (2 * b) ^ k * b * b :=
          add_le_add (mul_le_mul h1 g1 (norm_nonneg _) hk) (mul_le_mul h2 g2 (norm_nonneg _) hk)
      _ = (2 * b) ^ (k + 1) * b := by ring

/-- `|a_k| ≤ (2b + t + 1)^{k+1}` when `|G_{xy}| ≤ b` on `{v, e_i, e_j}` and `|Π_{vv}| ≤ t`. -/
private lemma taylor_res_le {N : ℕ} (A M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) (u : Fin 3 → Fin N → ℝ) (hu0 : u 0 = v) (hu1 : u 1 = eI i) (hu2 : u 2 = eI j)
    {b t : ℝ} (hb : ∀ a c, ‖ent (GW A M z) (u a) (u c)‖ ≤ b) (ht : ‖ent (piW A z) v v‖ ≤ t)
    (k : ℕ) : ‖resCoeffW A M z v i j k‖ ≤ (2 * b + t + 1) ^ (k + 1) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  have hw := taylor_word_le (GW A M z) i j u hu1 hu2 hb k 0 0
  rw [hu0] at hw
  have hc : ‖ent (if k = 0 then piW A z else 0) v v‖ ≤ t := by
    split_ifs
    · exact ht
    · simpa [ent] using ht0
  have h1 : ‖resCoeffW A M z v i j k‖ ≤ (2 * b) ^ k * b + t := by
    unfold resCoeffW
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, taylor_ent_sub]
    exact (norm_sub_le _ _).trans (add_le_add hw hc)
  refine h1.trans ?_
  set B := 2 * b + t + 1 with hB
  have hB1 : 1 ≤ B := by linarith
  have h2 : (2 * b) ^ k ≤ B ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
  have h3 : (1 : ℝ) ≤ B ^ k := one_le_pow₀ hB1
  calc (2 * b) ^ k * b + t ≤ B ^ k * b + B ^ k * t :=
        add_le_add (mul_le_mul_of_nonneg_right h2 hb0) (le_mul_of_one_le_left ht0 h3)
    _ = B ^ k * (b + t) := by ring
    _ ≤ B ^ k * B := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = B ^ (k + 1) := (pow_succ _ _).symm

/-- `|f_n| ≤ (n + 1)^p (2b + t + 1)^{n+p}` under the hypotheses of `taylor_res_le`. -/
private lemma taylor_f_le {N : ℕ} (A M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) (u : Fin 3 → Fin N → ℝ) (hu0 : u 0 = v) (hu1 : u 1 = eI i) (hu2 : u 2 = eI j)
    {b t : ℝ} (hb : ∀ a c, ‖ent (GW A M z) (u a) (u c)‖ ≤ b) (ht : ‖ent (piW A z) v v‖ ≤ t)
    (p n : ℕ) :
    ‖fCoeff p (resCoeffW A M z v i j) n‖ ≤ ((n : ℝ) + 1) ^ p * (2 * b + t + 1) ^ (n + p) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  exact norm_fCoeff_le p (by linarith) n fun k _ =>
    taylor_res_le A M z v i j u hu0 hu1 hu2 hb ht k

/-- The 2×2 perturbation: if `|G_{xy}(W)| ≤ g` on `{u₀, e_i, e_j}` and `18|s − W_{ij}| g ≤ 1`, then
`|G_{xy}(W^{(ij),s})| ≤ 18 g` there. -/
private lemma taylor_pert {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (u : Fin 3 → Fin N → ℝ)
    (hu1 : u 1 = eI i) (hu2 : u 2 = eI j) {g : ℝ} (hg : ∀ a c, ‖ent (GW A Wm z) (u a) (u c)‖ ≤ g)
    {s : ℝ} (hs : 18 * |s - Wm i j| * g ≤ 1) :
    ∀ a c, ‖ent (GW A (Wupd Wm i j s) z) (u a) (u c)‖ ≤ 18 * g := by
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg 0 0)
  have hid := taylor_res_id hA hW hz i j (Wm i j) s
  rw [taylor_Wupd_self hW] at hid
  set G := GW A Wm z with hG
  set Gs := GW A (Wupd Wm i j s) z with hGs
  set d : ℝ := s - Wm i j with hd
  have hGs' : Gs = G + (-(d : ℂ)) • (G * deltaW i j * Gs) := by
    rw [← hid]; abel
  set f : Fin 3 → Fin 3 → ℝ := fun a c => ‖ent Gs (u a) (u c)‖ with hf
  set S : ℝ := ∑ a, ∑ c, f a c with hS
  have hf0 : ∀ a c, 0 ≤ f a c := fun a c => norm_nonneg _
  have hfS : ∀ a c, f a c ≤ S := by
    intro a c
    have h1 : f a c ≤ ∑ c', f a c' :=
      Finset.single_le_sum (f := fun c' => f a c') (fun c' _ => hf0 a c') (Finset.mem_univ c)
    have h2 : ∑ c', f a c' ≤ S :=
      Finset.single_le_sum (f := fun a' => ∑ c', f a' c')
        (fun a' _ => Finset.sum_nonneg fun c' _ => hf0 a' c') (Finset.mem_univ a)
    linarith
  have hcol : ∀ c, f 2 c + f 1 c ≤ S := by
    intro c
    have h1 : f 2 c + f 1 c ≤ ∑ a, f a c := by
      rw [Fin.sum_univ_three]
      linarith [hf0 0 c]
    have h2 : ∑ a, f a c ≤ S := by
      rw [hS, Finset.sum_comm]
      exact Finset.single_le_sum (f := fun c' => ∑ a, f a c')
        (fun c' _ => Finset.sum_nonneg fun a _ => hf0 a c') (Finset.mem_univ c)
    linarith
  have hent : ∀ a c, f a c ≤ g + |d| * (g * S) := by
    intro a c
    have e : ent Gs (u a) (u c) =
        ent G (u a) (u c) + (-(d : ℂ)) * ent (G * deltaW i j * Gs) (u a) (u c) := by
      conv_lhs => rw [hGs']
      rw [taylor_ent_add, taylor_ent_smul]
    have hD := taylor_ent_delta_le G Gs i j (u a) (u c)
    have ga := hg a 1
    have gb := hg a 2
    rw [hu1] at ga
    rw [hu2] at gb
    have hD' : ‖ent (G * deltaW i j * Gs) (u a) (u c)‖ ≤ g * S := by
      refine hD.trans ?_
      have k1 : ‖ent Gs (eI j) (u c)‖ = f 2 c := by simp [hf, hu2]
      have k2 : ‖ent Gs (eI i) (u c)‖ = f 1 c := by simp [hf, hu1]
      rw [k1, k2]
      have := hcol c
      calc _ ≤ g * f 2 c + g * f 1 c :=
            add_le_add (mul_le_mul_of_nonneg_right ga (hf0 2 c))
              (mul_le_mul_of_nonneg_right gb (hf0 1 c))
        _ = g * (f 2 c + f 1 c) := by ring
        _ ≤ g * S := mul_le_mul_of_nonneg_left this hg0
    change ‖ent Gs (u a) (u c)‖ ≤ _
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hg a c) ?_)
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hD' (abs_nonneg _)
  have hsum : S ≤ 9 * (g + |d| * (g * S)) := by
    calc S ≤ ∑ _a : Fin 3, ∑ _c : Fin 3, (g + |d| * (g * S)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => hent a c
      _ = 9 * (g + |d| * (g * S)) := by simp; ring
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => hf0 a c
  have hS18 : S ≤ 18 * g := by
    have h1 : 9 * (|d| * (g * S)) ≤ S / 2 := by
      have : 18 * |d| * g * S ≤ S := by nlinarith
      nlinarith
    nlinarith
  intro a c
  exact (hfS a c).trans hS18

/-! ## The trivial bound `|G_{xy}| ≤ |x||y| / Im z` -/

private lemma taylor_testNorm_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

private lemma taylor_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
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

/-- `|G_{xy}| ≤ |x||y| / Im z` for a real symmetric `W + A`. -/
private lemma taylor_ent_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x y : Fin N → ℝ) :
    ‖ent (GW A Wm z) x y‖ ≤ z.im⁻¹ * testNorm x * testNorm y := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := taylor_eig_decomp (hW'.add hA)
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    Matrix.inv_eq_right_inv (taylor_right_inv hUU hUU' hMU hne)
  have hsq : ∀ v : Fin N → ℝ, ∑ k, (Uᵀ *ᵥ v) k ^ 2 = testNorm v ^ 2 := by
    intro v
    rw [← taylor_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v]
    unfold testNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [hG, taylor_ent_sandwich]
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
        rw [hsq, hsq, Real.sqrt_sq (by unfold testNorm; positivity),
          Real.sqrt_sq (by unfold testNorm; positivity)]
    _ = _ := by ring

private lemma taylor_testNorm_eI {N : ℕ} (i : Fin N) : testNorm (eI i) = 1 := by
  simp [testNorm, eI, Pi.single_apply]

/-- The test vectors `(v, e_i, e_j)`. -/
private def taylorU {N : ℕ} (v : Fin N → ℝ) (i j : Fin N) : Fin 3 → Fin N → ℝ := ![v, eI i, eI j]

private lemma taylorU_testNorm {N : ℕ} {v : Fin N → ℝ} (hv : testNorm v = 1) (i j : Fin N)
    (a : Fin 3) : testNorm (taylorU v i j a) = 1 := by
  fin_cases a <;> simp [taylorU, hv, taylor_testNorm_eI]

/-! ## The remainder of the re-expansion -/

/-- `R_l = f_l(W) − ∑_{k ≤ 4p−l} C(l+k, l) W_{ij}^k f_{l+k}(W^{(ij),0})`. -/
private def taylorRem {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) (p l : ℕ) : ℂ :=
  fCoeff p (resCoeffW A Wm z v i j) l -
    ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * ((Wm i j : ℝ) : ℂ) ^ k *
      fCoeff p (resCoeffW A (Wupd Wm i j 0) z v i j) (l + k)

private lemma taylor_measurable_rem {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (p l : ℕ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => taylorRem A Wm z v i j p l := by
  unfold taylorRem
  refine (taylor_measurable_fCoeff p l fun k => taylor_measurable_res A z v i j k).sub ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  refine (measurable_const.mul ?_).mul (taylor_measurable_fUpd A z v i j p (l + k) 0)
  exact (Complex.measurable_ofReal.comp (measurable_pi_iff.1
    (measurable_pi_iff.1 measurable_id i) j)).pow_const k

private lemma taylor_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- The remainder on the a priori event: `|G_{xy}| ≤ g` on `{v, e_i, e_j}`, `|Π_{vv}| ≤ t` and
`36 |W_{ij}| g ≤ 1` give `|R_l| ≤ (4p+1)! (4p+2)^p (36g + t + 1)^{5p+1} |W_{ij}|^{4p+1−l}`. -/
private lemma taylor_rem_good {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i j : Fin N) {g t : ℝ}
    (hg : ∀ a c, ‖ent (GW A Wm z) (taylorU v i j a) (taylorU v i j c)‖ ≤ g)
    (ht : ‖ent (piW A z) v v‖ ≤ t) (hξ : 36 * |Wm i j| * g ≤ 1) (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖taylorRem A Wm z v i j p l‖ ≤ ((4 * p + 1).factorial : ℝ) *
      ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p * (2 * (18 * g) + t + 1) ^ (4 * p + 1 + p)) *
      |Wm i j| ^ (4 * p - l + 1) := by
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg 0 0)
  have ha : ∀ k x, HasDerivAt (fun y => resCoeffW A (Wupd Wm i j y) z v i j k)
      (((k : ℂ) + 1) * resCoeffW A (Wupd Wm i j x) z v i j (k + 1)) x :=
    fun k x => taylor_hasDerivAt_resCoeffW hA hW hz v i j k x
  have hidx : l + (4 * p - l) + 1 = 4 * p + 1 := by omega
  have hT := fCoeff_taylor p ha l (4 * p - l) 0 (Wm i j)
    ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p * (2 * (18 * g) + t + 1) ^ (4 * p + 1 + p)) (fun s hs => by
      rw [zero_add, hidx]
      have hs' := taylor_abs_le_of_mem_uIcc hs
      have hd : 18 * |s - Wm i j| * g ≤ 1 := by
        have : |s - Wm i j| ≤ 2 * |Wm i j| := by
          calc |s - Wm i j| ≤ |s| + |Wm i j| := abs_sub _ _
            _ ≤ 2 * |Wm i j| := by linarith
        nlinarith
      have hp := taylor_pert hA hW hz i j (taylorU v i j) (by simp [taylorU]) (by simp [taylorU])
        hg hd
      exact taylor_f_le A (Wupd Wm i j s) z v i j (taylorU v i j) (by simp [taylorU])
        (by simp [taylorU]) (by simp [taylorU]) hp ht p (4 * p + 1))
  rw [zero_add, hidx, taylor_Wupd_self hW] at hT
  exact hT

/-- `|f_n(W)| ≤ (4p+1)^p (4N)^{5p}` for `n ≤ 4p` and a symmetric `W`, when `η⁻¹, t ≤ N`. -/
private lemma taylor_f_det {N : ℕ} (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N)
    {v : Fin N → ℝ} (hv : testNorm v = 1) (i j : Fin N) {t : ℝ}
    (ht : ‖ent (piW A z) v v‖ ≤ t) (htN : t ≤ N) (p n : ℕ) (hn : n ≤ 4 * p) :
    ‖fCoeff p (resCoeffW A Wm z v i j) n‖ ≤ ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : ∀ a c, ‖ent (GW A Wm z) (taylorU v i j a) (taylorU v i j c)‖ ≤ z.im⁻¹ := by
    intro a c
    have h := taylor_ent_le hA hW hz (taylorU v i j a) (taylorU v i j c)
    rwa [taylorU_testNorm hv, taylorU_testNorm hv, mul_one, mul_one] at h
  have h := taylor_f_le A Wm z v i j (taylorU v i j) (by simp [taylorU]) (by simp [taylorU])
    (by simp [taylorU]) hb ht p n
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  have hη0 : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz.le
  have hB : 2 * z.im⁻¹ + t + 1 ≤ 4 * N := by linarith
  have hB1 : 1 ≤ 2 * z.im⁻¹ + t + 1 := by linarith
  have hn1 : (n : ℝ) + 1 ≤ ((4 * p + 1 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 4 * p := by exact_mod_cast hn
    push_cast; linarith
  refine h.trans ?_
  calc ((n : ℝ) + 1) ^ p * (2 * z.im⁻¹ + t + 1) ^ (n + p)
      ≤ ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (n + p) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hn1 p)
          (pow_le_pow_left₀ (by linarith) hB _) (by positivity) (by positivity)
    _ ≤ ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega)) (by positivity)

/-- The constant `(4p+1)^p (1 + (4p+1) 2^{4p})` of the deterministic remainder bound. -/
private def taylorKR (p : ℕ) : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ p * (1 + (4 * p + 1) * 2 ^ (4 * p))

private lemma taylorKR_nonneg (p : ℕ) : 0 ≤ taylorKR p := by
  unfold taylorKR; positivity

/-- The deterministic remainder bound `|R_l| ≤ K (4N)^{5p} (1 + |W_{ij}|^{4p})`. -/
private lemma taylor_rem_det {N : ℕ} (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N)
    {v : Fin N → ℝ} (hv : testNorm v = 1) (i j : Fin N) {t : ℝ}
    (ht : ‖ent (piW A z) v v‖ ≤ t) (htN : t ≤ N) (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖taylorRem A Wm z v i j p l‖ ≤ taylorKR p * (4 * N) ^ (5 * p) * (1 + |Wm i j| ^ (4 * p)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set F : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) with hF
  have hF0 : 0 ≤ F := by positivity
  set X : ℝ := |Wm i j| with hX
  have hX0 : 0 ≤ X := abs_nonneg _
  have hW0 := taylor_Wupd_symm hW i j 0
  have hterm : ∀ k ∈ Finset.range (4 * p - l + 1),
      ‖((l + k).choose l : ℂ) * ((Wm i j : ℝ) : ℂ) ^ k *
          fCoeff p (resCoeffW A (Wupd Wm i j 0) z v i j) (l + k)‖ ≤
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
    have hf := taylor_f_det hN hA hW0 hz hηN hv i j ht htN p (l + k) (by omega)
    calc ((l + k).choose l : ℝ) * |Wm i j| ^ k *
          ‖fCoeff p (resCoeffW A (Wupd Wm i j 0) z v i j) (l + k)‖
        ≤ 2 ^ (4 * p) * (1 + X ^ (4 * p)) * F := by
          gcongr
      _ = 2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F) := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfl := taylor_f_det hN hA hW hz hηN hv i j ht htN p l hl
  have hcard : ((4 * p - l + 1 : ℕ) : ℝ) ≤ 4 * p + 1 := by
    have : 4 * p - l + 1 ≤ 4 * p + 1 := by omega
    exact_mod_cast this
  unfold taylorRem
  refine (norm_sub_le _ _).trans ?_
  have hA0 : 0 ≤ 2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F) := by positivity
  have hX1 : F ≤ (1 + X ^ (4 * p)) * F :=
    le_mul_of_one_le_left hF0 (by linarith [pow_nonneg hX0 (4 * p)])
  calc _ ≤ F + ((4 * p - l + 1 : ℕ) : ℝ) * (2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F)) :=
        add_le_add hfl hsum
    _ ≤ (1 + X ^ (4 * p)) * F + (4 * p + 1) * (2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F)) := by
        gcongr
    _ = taylorKR p * (4 * N) ^ (5 * p) * (1 + X ^ (4 * p)) := by
        unfold taylorKR; rw [hF]; ring

/-! ## The entry `W_{ij}`: Markov, independence, moments -/

private lemma taylor_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

/-- `|y| ≤ N^{ε − 1/2}` with probability `≥ 1 − N^{−D}`, from the moments of `√N y` (Markov). -/
private lemma taylor_markov (C : ℕ → ℝ) (ε D : ℝ) (hε : 0 < ε) :
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
    taylor_le_rpow (zero_le_one.trans (le_max_right _ _)) (by positivity)
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
private lemma taylor_indep {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
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
private lemma taylor_moment_entry {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
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

/-! ## Expectations: the re-expansion and Lemma 7.7 -/

/-- The moment constant `2 K_R² 4^{10p} (1 + max(C_{8p}, 0))`. -/
private def taylorKM (p : ℕ) (C : ℕ → ℝ) : ℝ :=
  2 * taylorKR p ^ 2 * 4 ^ (10 * p) * (1 + max (C (8 * p)) 0)

/-- Expectation of the re-expansion along `α = (i, j)`: by independence of `W_{ij}` and
`W^{(ij),0}`, `E f_l(W) = ∑_k C(l+k, l) E W_{ij}^k E f_{l+k}(W^{(ij),0}) + E R_l`; Lemma 7.7 bounds
`|E R_l| ≤ 2 N^δ Γ` on the event `|R_l| ≤ Γ`. -/
private lemma taylor_expect {N : ℕ} (hN : 1 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N) {v : Fin N → ℝ}
    (hv : testNorm v = 1) {t : ℝ} (ht : ‖ent (piW A z) v v‖ ≤ t) (htN : t ≤ N) {C : ℕ → ℝ}
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N)
    (p l : ℕ) (hl : l ≤ 4 * p) {δ D Γ : ℝ} (hδ : 0 ≤ δ) (hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ D)
    (hΓ : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ Γ) (hK : taylorKM p C ≤ N)
    (hev : HighProbAt N D {ω | ‖taylorRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤ Γ}) :
    (∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) l) =
      (∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
        (∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ k) *
        (∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) (l + k))) +
        ∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l ∧
    ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤ 2 * (N : ℝ) ^ δ * Γ := by
  set i := α.1.1 with hi
  set j := α.1.2 with hj
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hWm : Measurable W :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => hW.measurable a b
  have hξm : Measurable fun ω => W ω i j := hW.measurable i j
  set F0 : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) with hF0
  have hF0m : ∀ n, AEStronglyMeasurable fun ω =>
      fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) n :=
    fun n => ((taylor_measurable_fUpd A z v i j p n 0).comp hWm).aestronglyMeasurable
  have hFm : AEStronglyMeasurable fun ω => fCoeff p (resCoeffW A (W ω) z v i j) l :=
    ((taylor_measurable_fCoeff p l fun k => taylor_measurable_res A z v i j k).comp
      hWm).aestronglyMeasurable
  have hF0b : ∀ n ≤ 4 * p, ∀ ω, ‖fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) n‖ ≤ F0 :=
    fun n hn ω => taylor_f_det hN hA (taylor_Wupd_symm (hW.symm ω) i j 0) hz hηN hv i j ht htN p
      n hn
  have hFb : ∀ ω, ‖fCoeff p (resCoeffW A (W ω) z v i j) l‖ ≤ F0 :=
    fun ω => taylor_f_det hN hA (hW.symm ω) hz hηN hv i j ht htN p l hl
  have hFi : Integrable fun ω => fCoeff p (resCoeffW A (W ω) z v i j) l :=
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
      (W ω i j : ℂ) ^ k * fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) (l + k) := by
    intro k hk
    have hk' : k ≤ 4 * p - l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    exact (hyi k).mul_bdd (hF0m (l + k)) (ae_of_all _ (hF0b (l + k) (by omega)))
  have hprod : ∀ k : ℕ, ∫ ω, (W ω i j : ℂ) ^ k *
      fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) (l + k) =
      (∫ ω, (W ω i j : ℂ) ^ k) * ∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) (l + k) :=
    fun k => ((taylor_indep hW α).symm.comp (hpowm k)
      (taylor_measurable_fCoeff p (l + k) fun k' =>
        taylor_measurable_res A z v i j k')).integral_fun_mul_eq_mul_integral
      (hym' k) (hF0m (l + k))
  set Rf : Ω → ℂ := fun ω => taylorRem A (W ω) z v i j p l with hRf
  set Sf : Ω → ℂ := fun ω => ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
      ((W ω i j : ℂ) ^ k * fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) (l + k)) with hSf
  have hSi : Integrable Sf := integrable_finsetSum _ fun k hk => (hprodi k hk).const_mul _
  have hdec : ∀ ω, fCoeff p (resCoeffW A (W ω) z v i j) l = Sf ω + Rf ω := by
    intro ω
    simp only [hSf, hRf, taylorRem]
    rw [Finset.sum_congr rfl fun k _ => (mul_assoc ((l + k).choose l : ℂ) ((W ω i j : ℂ) ^ k)
      (fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) (l + k))).symm]
    ring
  have hRi : Integrable Rf := by
    have : Rf = fun ω => fCoeff p (resCoeffW A (W ω) z v i j) l - Sf ω := by
      funext ω; rw [hdec ω]; ring
    rw [this]; exact hFi.sub hSi
  refine ⟨?_, ?_⟩
  · calc (∫ ω, fCoeff p (resCoeffW A (W ω) z v i j) l)
        = ∫ ω, (Sf ω + Rf ω) := integral_congr_ae (ae_of_all _ hdec)
      _ = (∫ ω, Sf ω) + ∫ ω, Rf ω := integral_add hSi hRi
      _ = _ := by
          congr 1
          rw [hSf, integral_finsetSum _ fun k hk => (hprodi k hk).const_mul _]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, hprod k]
          ring
  · -- Lemma 7.7
    set KR := taylorKR p with hKR
    have hKR0 : 0 ≤ KR := taylorKR_nonneg p
    set Cr : ℝ := ((10 * p + 1 : ℕ) : ℝ) with hCr
    set C' : ℝ := max (C (8 * p)) 0 with hC'
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hRb : ∀ ω, ‖Rf ω‖ ≤ KR * (4 * N) ^ (5 * p) * (1 + |W ω i j| ^ (4 * p)) := fun ω =>
      taylor_rem_det hN hA (hW.symm ω) hz hηN hv i j ht htN p l hl
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
      (((taylor_measurable_rem A z v i j p l).comp hWm).norm.pow_const 2).aestronglyMeasurable
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
        _ = taylorKM p C * (N : ℝ) ^ (10 * p) := by
            unfold taylorKM; rw [mul_pow]; ring
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

/-! ## The a priori event -/

/-- The constant `(4p+1)! (4p+2)^p (37(1 + τ⁻¹))^{5p+1} / τ^p`. -/
private def taylorK1 (τ : ℝ) (p : ℕ) : ℝ :=
  ((4 * p + 1).factorial : ℝ) * (((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
    (37 * (1 + τ⁻¹)) ^ (4 * p + 1 + p) / τ ^ p

private lemma taylorK1_nonneg {τ : ℝ} (hτ : 0 < τ) (p : ℕ) : 0 ≤ taylorK1 τ p := by
  unfold taylorK1; positivity

/-- The union bound: nine events of probability `≤ N^{−(D−1)}` and one of probability `≤ N^{−D}`
have total probability `≤ N^{−(D−5)}`, for `N ≥ 2`. -/
private lemma taylor_prob_bound {Ω : Type} [MeasureSpace Ω] {N : ℕ} (hN : 2 ≤ N) {D : ℝ}
    (E : Fin 3 → Fin 3 → Set Ω) (Ξ S : Set Ω)
    (hE : ∀ a c, ℙ (E a c) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 1))))
    (hΞ : ℙ Ξᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) (hsub : Sᶜ ⊆ (⋃ a, ⋃ c, E a c) ∪ Ξᶜ) :
    ℙ Sᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 5))) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hx0 : 0 ≤ (N : ℝ) ^ (-(D - 1)) := Real.rpow_nonneg hNp.le _
  have hy0 : 0 ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hNp.le _
  have hyx : (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-(D - 1)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hx5 : 3 * (3 * (N : ℝ) ^ (-(D - 1))) + (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-(D - 5)) := by
    have e : (N : ℝ) ^ (-(D - 5)) = (N : ℝ) ^ (-(D - 1)) * (N : ℝ) ^ (4 : ℝ) := by
      rw [← Real.rpow_add hNp]; congr 1; ring
    have h4 : (16 : ℝ) ≤ (N : ℝ) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hNr 4
      norm_num at this
      linarith
    rw [e]
    have := mul_le_mul_of_nonneg_left h4 hx0
    linarith
  calc ℙ Sᶜ ≤ ℙ ((⋃ a, ⋃ c, E a c) ∪ Ξᶜ) := measure_mono hsub
    _ ≤ ℙ (⋃ a, ⋃ c, E a c) + ℙ Ξᶜ := measure_union_le _ _
    _ ≤ ∑ a, ∑ c, ℙ (E a c) + ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
        add_le_add ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun a _ => measure_iUnion_fintype_le _ _)) hΞ
    _ ≤ ∑ _a : Fin 3, ∑ _c : Fin 3, ENNReal.ofReal ((N : ℝ) ^ (-(D - 1))) +
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        gcongr with a _ c _
        exact hE a c
    _ = ENNReal.ofReal (3 * (3 * (N : ℝ) ^ (-(D - 1))) + (N : ℝ) ^ (-D)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_add (by positivity) hy0, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D - 5))) := ENNReal.ofReal_le_ofReal hx5

/-- On the a priori event of Lemma 12.6 (i) for the pairs in `{v, e_i, e_j}` and
`|W_{ij}| ≤ N^{δ/4 − 1/2}`, the remainder satisfies `|R_l| ≤ τ^p N^{l/2 − 2 − p}`. -/
private lemma taylor_event {N : ℕ} (hN : 2 ≤ N) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 120) {p : ℕ} (hp2 : 2 ≤ p) (h36 : 36 * (1 + τ⁻¹) ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    (hK1 : taylorK1 τ p ≤ (N : ℝ) ^ (1 / 10 : ℝ)) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) {v : Fin N → ℝ} (hv : testNorm v = 1)
    (hPi : ∀ x y : Fin N → ℝ, ‖ent (piW A z) x y‖ ≤ τ⁻¹ * testNorm x * testNorm y)
    {Ω : Type} [MeasureSpace Ω] {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hWs : ∀ ω, (W ω)ᵀ = W ω)
    {D : ℝ}
    (hr1 : ∀ x y : Fin N → ℝ, DomAt N (2 * (δ / 4)) (D - 1)
      (fun ω => ‖testBilin x (GW A (W ω) z - piW A z) y‖)
      (fun _ => (N : ℝ) ^ (2 * δ) * testNorm x * testNorm y))
    (i j : Fin N) (hξ : HighProbAt N D {ω | |W ω i j| ≤ (N : ℝ) ^ (δ / 4 - 1 / 2)})
    (l : ℕ) (hl : l ≤ 4 * p) :
    HighProbAt N (D - 5)
      {ω | ‖taylorRem A (W ω) z v i j p l‖ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p)} := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set u := taylorU v i j with hu
  have hun : ∀ a, testNorm (u a) = 1 := taylorU_testNorm hv i j
  set E : Fin 3 → Fin 3 → Set Ω := fun a c => {ω | (N : ℝ) ^ (2 * (δ / 4)) *
    ((N : ℝ) ^ (2 * δ) * testNorm (u a) * testNorm (u c)) <
      ‖testBilin (u a) (GW A (W ω) z - piW A z) (u c)‖} with hE
  set Ξ : Set Ω := {ω | |W ω i j| ≤ (N : ℝ) ^ (δ / 4 - 1 / 2)} with hΞ
  set e5 : ℝ := (N : ℝ) ^ (5 * δ / 2) with he5
  have he51 : 1 ≤ e5 := Real.one_le_rpow hN1 (by positivity)
  have he5e : (N : ℝ) ^ (2 * (δ / 4)) * (N : ℝ) ^ (2 * δ) = e5 := by
    rw [← Real.rpow_add hNp]; congr 1; ring
  set g : ℝ := e5 + τ⁻¹ with hg
  have hτi : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
  have hgle : g ≤ (1 + τ⁻¹) * e5 := by nlinarith
  -- the deterministic bound on the good event
  have hgood : ∀ ω, (∀ a c, ω ∉ E a c) → ω ∈ Ξ →
      ‖taylorRem A (W ω) z v i j p l‖ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) := by
    intro ω hωE hωΞ
    have hG : ∀ a c, ‖ent (GW A (W ω) z) (u a) (u c)‖ ≤ g := by
      intro a c
      have h1 := not_lt.1 (show ¬ ((N : ℝ) ^ (2 * (δ / 4)) *
        ((N : ℝ) ^ (2 * δ) * testNorm (u a) * testNorm (u c)) <
          ‖testBilin (u a) (GW A (W ω) z - piW A z) (u c)‖) from hωE a c)
      rw [hun, hun, mul_one, mul_one, he5e] at h1
      have h2 := hPi (u a) (u c)
      rw [hun, hun, mul_one, mul_one] at h2
      have hd : ent (GW A (W ω) z) (u a) (u c) =
          ent (GW A (W ω) z - piW A z) (u a) (u c) + ent (piW A z) (u a) (u c) := by
        rw [taylor_ent_sub]; ring
      rw [hd]
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    have hPv : ‖ent (piW A z) v v‖ ≤ τ⁻¹ := by
      have := hPi v v
      rwa [hv, mul_one, mul_one] at this
    have hξ0 : |W ω i j| ≤ (N : ℝ) ^ (δ / 4 - 1 / 2) := hωΞ
    have h36' : 36 * |W ω i j| * g ≤ 1 := by
      have hg0 : 0 ≤ g := by positivity
      calc 36 * |W ω i j| * g ≤ 36 * (N : ℝ) ^ (δ / 4 - 1 / 2) * ((1 + τ⁻¹) * e5) := by
            gcongr
        _ = (36 * (1 + τ⁻¹)) * ((N : ℝ) ^ (δ / 4 - 1 / 2) * e5) := by ring
        _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * ((N : ℝ) ^ (δ / 4 - 1 / 2) * e5) := by gcongr
        _ = (N : ℝ) ^ (1 / 4 + (δ / 4 - 1 / 2) + 5 * δ / 2) := by
            rw [he5, Real.rpow_add hNp, Real.rpow_add hNp]; ring
        _ ≤ (N : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have hR := taylor_rem_good hA (hWs ω) hz v i j hG hPv h36' p l hl
    refine hR.trans ?_
    have hB : 2 * (18 * g) + τ⁻¹ + 1 ≤ 37 * (1 + τ⁻¹) * e5 := by nlinarith
    have hB0 : 0 ≤ 2 * (18 * g) + τ⁻¹ + 1 := by positivity
    set q : ℕ := 4 * p + 1 + p with hq
    set r : ℕ := 4 * p - l + 1 with hr
    have hrc : (r : ℝ) = 4 * p - l + 1 := by
      rw [hr, Nat.cast_add, Nat.cast_sub hl]; push_cast; ring
    have hqc : (q : ℝ) = 5 * p + 1 := by rw [hq]; push_cast; ring
    have hBq : (2 * (18 * g) + τ⁻¹ + 1) ^ q ≤ (37 * (1 + τ⁻¹)) ^ q * (N : ℝ) ^ (5 * δ / 2 * q) := by
      calc (2 * (18 * g) + τ⁻¹ + 1) ^ q ≤ (37 * (1 + τ⁻¹) * e5) ^ q := pow_le_pow_left₀ hB0 hB q
        _ = (37 * (1 + τ⁻¹)) ^ q * (N : ℝ) ^ (5 * δ / 2 * q) := by
            rw [mul_pow, he5, Real.rpow_mul_natCast hNp.le]
    have hξr : |W ω i j| ^ r ≤ (N : ℝ) ^ ((δ / 4 - 1 / 2) * r) := by
      rw [Real.rpow_mul hNp.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (abs_nonneg _) hξ0 r
    have hexp : 1 / 10 + 5 * δ / 2 * q + (δ / 4 - 1 / 2) * r ≤ (l : ℝ) / 2 - 2 - p := by
      rw [hrc, hqc]
      have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have hL : (l : ℝ) ≤ 4 * p := by exact_mod_cast hl
      have hL0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have h1 : δ * (5 * p + 1) ≤ (5 * p + 1) / 120 := by nlinarith
      have h2 : δ * (4 * p - l + 1) ≤ (4 * p - l + 1) / 120 := by nlinarith
      nlinarith
    have hfac0 : (0 : ℝ) ≤ ((4 * p + 1).factorial : ℝ) := Nat.cast_nonneg _
    have hK1' : ((4 * p + 1).factorial : ℝ) * (((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
        (37 * (1 + τ⁻¹)) ^ q ≤ τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ) := by
      have h := hK1
      unfold taylorK1 at h
      rw [div_le_iff₀ (by positivity)] at h
      linarith
    calc ((4 * p + 1).factorial : ℝ) * ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
          (2 * (18 * g) + τ⁻¹ + 1) ^ q) * |W ω i j| ^ r
        ≤ ((4 * p + 1).factorial : ℝ) * ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
          ((37 * (1 + τ⁻¹)) ^ q * (N : ℝ) ^ (5 * δ / 2 * q))) *
            (N : ℝ) ^ ((δ / 4 - 1 / 2) * r) := by
          gcongr
      _ = (((4 * p + 1).factorial : ℝ) * (((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
            (37 * (1 + τ⁻¹)) ^ q) * ((N : ℝ) ^ (5 * δ / 2 * q) *
              (N : ℝ) ^ ((δ / 4 - 1 / 2) * r)) := by ring
      _ ≤ (τ ^ p * (N : ℝ) ^ (1 / 10 : ℝ)) * ((N : ℝ) ^ (5 * δ / 2 * q) *
              (N : ℝ) ^ ((δ / 4 - 1 / 2) * r)) := by gcongr
      _ = τ ^ p * (N : ℝ) ^ (1 / 10 + 5 * δ / 2 * q + (δ / 4 - 1 / 2) * r) := by
          rw [Real.rpow_add hNp, Real.rpow_add hNp]; ring
      _ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) := by
          gcongr
  -- the probability of the bad event
  have hsub : {ω | ‖taylorRem A (W ω) z v i j p l‖ ≤
      τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p)}ᶜ ⊆ (⋃ a, ⋃ c, E a c) ∪ Ξᶜ := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists,
      not_not] at hc
    exact hω (hgood ω hc.1 hc.2)
  exact taylor_prob_bound hN E Ξ _ (fun a c => hr1 (u a) (u c)) hξ hsub

/-! ## The downward recursion -/

private lemma taylor_sc_mul {N : ℕ} (hN : 1 ≤ N) (n k : ℕ) :
    (N : ℝ) ^ (-(n : ℝ) / 2) * (N : ℝ) ^ (-(k : ℝ) / 2) = (N : ℝ) ^ (-((n + k : ℕ) : ℝ) / 2) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  rw [← Real.rpow_add hNp]; push_cast; ring_nf

/-- The downward recursion of Lemma 7.16 for one entry: from
`y_l = ∑_{k ≤ 4p−l} C(l+k, l) μ_k x_{l+k} + r_l` with `μ_0 = 1`, `μ_1 = 0`, `|μ_k| ≤ N^{−k/2} C_k`
and `C(l+k, l) C_k ≤ L`, the defect `x_l − y_l + r_l` is bounded by the orders `≥ l + 2`. -/
private lemma taylor_chain {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (x y r μ : ℕ → ℂ) (Cm : ℕ → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hid : ∀ l ≤ 4 * p, y l = (∑ k ∈ Finset.range (4 * p - l + 1),
      ((l + k).choose l : ℂ) * μ k * x (l + k)) + r l)
    (hμ0 : μ 0 = 1) (hμ1 : μ 1 = 0) (hμ : ∀ k, ‖μ k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * Cm k)
    (hLc : ∀ l k, l + k ≤ 4 * p → ((l + k).choose l : ℝ) * Cm k ≤ L) :
    ∀ l ≤ 4 * p, (N : ℝ) ^ (-(l : ℝ) / 2) * ‖x l - y l + r l‖ ≤
      (1 + 8 * p * L) ^ (4 * p - l) * ∑ k ∈ Finset.Icc (l + 2) (4 * p),
        (N : ℝ) ^ (-(k : ℝ) / 2) * (‖y k‖ + ‖r k‖) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  set Q : ℝ := 1 + 8 * p * L with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ 8 * p * L := by positivity
    linarith
  set T : ℕ → ℝ := fun l => ∑ k ∈ Finset.Icc (l + 2) (4 * p),
    (N : ℝ) ^ (-(k : ℝ) / 2) * (‖y k‖ + ‖r k‖) with hT
  have hterm0 : ∀ k : ℕ, 0 ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * (‖y k‖ + ‖r k‖) := fun k => by positivity
  have hT0 : ∀ l, 0 ≤ T l := fun l => Finset.sum_nonneg fun k _ => hterm0 k
  have hTmono : ∀ l m, l ≤ m → T m ≤ T l := by
    intro l m hlm
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hterm0 k
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hTterm : ∀ l m, l + 2 ≤ m → m ≤ 4 * p →
      (N : ℝ) ^ (-(m : ℝ) / 2) * (‖y m‖ + ‖r m‖) ≤ T l := by
    intro l m h1 h2
    exact Finset.single_le_sum (f := fun k : ℕ => (N : ℝ) ^ (-(k : ℝ) / 2) * (‖y k‖ + ‖r k‖))
      (fun k _ => hterm0 k) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  suffices H : ∀ d, ∀ l ≤ 4 * p, 4 * p - l = d →
      (N : ℝ) ^ (-(l : ℝ) / 2) * ‖x l - y l + r l‖ ≤ Q ^ d * T l from
    fun l hl => H _ l hl rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l hl hd
    have hsc0 : 0 ≤ (N : ℝ) ^ (-(l : ℝ) / 2) := Real.rpow_nonneg hNp.le _
    have hx : x l - y l + r l = -∑ k ∈ Finset.range (4 * p - l),
        ((l + (k + 1)).choose l : ℂ) * μ (k + 1) * x (l + (k + 1)) := by
      rw [hid l hl, Finset.sum_range_succ']
      simp only [add_zero, Nat.choose_self, Nat.cast_one, one_mul, hμ0]
      ring
    have hbd : ∀ k ∈ Finset.range (4 * p - l), (N : ℝ) ^ (-(l : ℝ) / 2) *
        ‖((l + (k + 1)).choose l : ℂ) * μ (k + 1) * x (l + (k + 1))‖ ≤
          2 * L * Q ^ (d - 1) * T l := by
      intro k hk
      have hk' : k + 1 ≤ 4 * p - l := Finset.mem_range.1 hk
      have hQd : 0 ≤ 2 * L * Q ^ (d - 1) * T l := by
        have := hT0 l; positivity
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp [hμ1, hQd]
      · set m := l + (k + 1) with hm
        have hm2 : l + 2 ≤ m := by omega
        have hm4 : m ≤ 4 * p := by omega
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have h1 := hμ (k + 1)
        have h2 := hLc l (k + 1) hm4
        have hcm : 0 ≤ Cm (k + 1) := by
          have := (norm_nonneg _).trans h1
          exact nonneg_of_mul_nonneg_right this (Real.rpow_pos_of_pos hNp _)
        have hscm : (N : ℝ) ^ (-(l : ℝ) / 2) * (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) =
            (N : ℝ) ^ (-(m : ℝ) / 2) := by
          rw [taylor_sc_mul hN l (k + 1)]
        have hxm : (N : ℝ) ^ (-(m : ℝ) / 2) * ‖x m‖ ≤ 2 * Q ^ (d - 1) * T l := by
          have e1 : ‖x m‖ ≤ ‖x m - y m + r m‖ + (‖y m‖ + ‖r m‖) := by
            have : x m = (x m - y m + r m) + y m - r m := by ring
            calc ‖x m‖ = ‖(x m - y m + r m) + y m - r m‖ := by rw [← this]
              _ ≤ ‖(x m - y m + r m) + y m‖ + ‖r m‖ := norm_sub_le _ _
              _ ≤ ‖x m - y m + r m‖ + ‖y m‖ + ‖r m‖ := by gcongr; exact norm_add_le _ _
              _ = _ := by ring
          have hih := ih (4 * p - m) (by omega) m hm4 rfl
          have hpow : Q ^ (4 * p - m) ≤ Q ^ (d - 1) := pow_le_pow_right₀ hQ1 (by omega)
          have hTm := hTmono l m (by omega)
          have hsm0 : 0 ≤ (N : ℝ) ^ (-(m : ℝ) / 2) := Real.rpow_nonneg hNp.le _
          have hQ0 : 1 ≤ Q ^ (d - 1) := one_le_pow₀ hQ1
          calc (N : ℝ) ^ (-(m : ℝ) / 2) * ‖x m‖
              ≤ (N : ℝ) ^ (-(m : ℝ) / 2) * ‖x m - y m + r m‖ +
                (N : ℝ) ^ (-(m : ℝ) / 2) * (‖y m‖ + ‖r m‖) := by
                rw [← mul_add]; exact mul_le_mul_of_nonneg_left e1 hsm0
            _ ≤ Q ^ (4 * p - m) * T m + T l := add_le_add hih (hTterm l m hm2 hm4)
            _ ≤ Q ^ (d - 1) * T l + Q ^ (d - 1) * T l :=
                add_le_add ((mul_le_mul_of_nonneg_right hpow (hT0 m)).trans
                  (mul_le_mul_of_nonneg_left hTm (by positivity)))
                  (le_mul_of_one_le_left (hT0 l) hQ0)
            _ = 2 * Q ^ (d - 1) * T l := by ring
        calc (N : ℝ) ^ (-(l : ℝ) / 2) * (((m.choose l : ℕ) : ℝ) * ‖μ (k + 1)‖ * ‖x m‖)
            ≤ (N : ℝ) ^ (-(l : ℝ) / 2) * (((m.choose l : ℕ) : ℝ) *
                ((N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) * Cm (k + 1)) * ‖x m‖) := by gcongr
          _ = (((m.choose l : ℕ) : ℝ) * Cm (k + 1)) *
                (((N : ℝ) ^ (-(l : ℝ) / 2) * (N : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2)) * ‖x m‖) := by
                ring
          _ = (((m.choose l : ℕ) : ℝ) * Cm (k + 1)) * ((N : ℝ) ^ (-(m : ℝ) / 2) * ‖x m‖) := by
                rw [hscm]
          _ ≤ L * (2 * Q ^ (d - 1) * T l) := by
                refine mul_le_mul h2 hxm (by positivity) hL
          _ = 2 * L * Q ^ (d - 1) * T l := by ring
    have hsum : (N : ℝ) ^ (-(l : ℝ) / 2) * ‖x l - y l + r l‖ ≤
        (d : ℝ) * (2 * L * Q ^ (d - 1) * T l) := by
      rw [hx, norm_neg]
      calc (N : ℝ) ^ (-(l : ℝ) / 2) * ‖∑ k ∈ Finset.range (4 * p - l),
            ((l + (k + 1)).choose l : ℂ) * μ (k + 1) * x (l + (k + 1))‖
          ≤ (N : ℝ) ^ (-(l : ℝ) / 2) * ∑ k ∈ Finset.range (4 * p - l),
            ‖((l + (k + 1)).choose l : ℂ) * μ (k + 1) * x (l + (k + 1))‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) hsc0
        _ = ∑ k ∈ Finset.range (4 * p - l), (N : ℝ) ^ (-(l : ℝ) / 2) *
            ‖((l + (k + 1)).choose l : ℂ) * μ (k + 1) * x (l + (k + 1))‖ := Finset.mul_sum _ _ _
        _ ≤ ∑ _k ∈ Finset.range (4 * p - l), 2 * L * Q ^ (d - 1) * T l := Finset.sum_le_sum hbd
        _ = (d : ℝ) * (2 * L * Q ^ (d - 1) * T l) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hd]
    refine hsum.trans ?_
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · simp [hT0 l]
    · have hd4 : (d : ℝ) ≤ 4 * p := by
        have : d ≤ 4 * p := by omega
        exact_mod_cast this
      have hpow : Q ^ d = Q ^ (d - 1) * Q := by
        rw [← pow_succ]; congr 1; omega
      have hQd0 : 0 ≤ Q ^ (d - 1) * T l := by have := hT0 l; positivity
      calc (d : ℝ) * (2 * L * Q ^ (d - 1) * T l) = ((d : ℝ) * (2 * L)) * (Q ^ (d - 1) * T l) := by
            ring
        _ ≤ Q * (Q ^ (d - 1) * T l) := by
            refine mul_le_mul_of_nonneg_right ?_ hQd0
            nlinarith
        _ = Q ^ d * T l := by rw [hpow]; ring

/-- The constant `L = 2^{4p} ∑_{k ≤ 4p} max(C_k, 0)` of the recursion. -/
private def taylorL (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  2 ^ (4 * p) * ∑ k ∈ Finset.range (4 * p + 1), max (C k) 0

private lemma taylorL_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ taylorL C p := by
  unfold taylorL
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => le_max_right _ _)

private lemma taylorL_ge {C : ℕ → ℝ} {p n k : ℕ} (hnk : n + k ≤ 4 * p) :
    ((n + k).choose n : ℝ) * max (C k) 0 ≤ taylorL C p := by
  unfold taylorL
  have h1 : ((n + k).choose n : ℝ) ≤ 2 ^ (4 * p) := by
    have := Nat.choose_le_two_pow (n + k) n
    have h2 : 2 ^ (n + k) ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by norm_num) hnk
    exact_mod_cast this.trans h2
  have h3 : max (C k) 0 ≤ ∑ j ∈ Finset.range (4 * p + 1), max (C j) 0 :=
    Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _)
      (Finset.mem_range.2 (by omega))
  exact mul_le_mul h1 h3 (le_max_right _ _) (by positivity)

/-- Summation over the entries: the weighted coefficient at `W^{(α),0}` is bounded by the
weighted coefficient at `W`, the remainders and the orders `≥ n + 2`. -/
private lemma taylor_assemble {ι : Type*} [Fintype ι] {N : ℕ} (hN : 1 ≤ N) (p n : ℕ)
    (hn4 : n ≤ 4 * p) (s : ι → ℂ) (hs : ∀ α, ‖s α‖ ≤ 1) (x y r : ι → ℕ → ℂ)
    (Y : ι → ℕ → ℝ) (hY : ∀ α k, ‖y α k‖ ≤ Y α k) {B E Q : ℝ} (hQ1 : 1 ≤ Q)
    (hB : (N : ℝ) ^ (-(n : ℝ) / 2) * ‖∑ α, s α * y α n‖ ≤ B) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E)
    (hE : ∀ l ≤ 4 * p, (N : ℝ) ^ (-(l : ℝ) / 2) * ∑ α, ‖r α l‖ ≤ 2 * E)
    (hchain : ∀ α, (N : ℝ) ^ (-(n : ℝ) / 2) * ‖x α n - y α n + r α n‖ ≤
      Q ^ (4 * p - n) * ∑ k ∈ Finset.Icc (n + 2) (4 * p),
        (N : ℝ) ^ (-(k : ℝ) / 2) * (‖y α k‖ + ‖r α k‖)) :
    (N : ℝ) ^ (-(n : ℝ) / 2) * ‖∑ α, s α * x α n‖ ≤
      (3 + 8 * p) * Q ^ (4 * p) * (B + E + ∑ k ∈ Finset.Icc (n + 2) (4 * p),
        (N : ℝ) ^ (-(k : ℝ) / 2) * ∑ α, Y α k) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  set sc : ℕ → ℝ := fun k => (N : ℝ) ^ (-(k : ℝ) / 2) with hsc
  have hsc0 : ∀ k, 0 ≤ sc k := fun k => Real.rpow_nonneg hNp.le _
  set tail : ℝ := ∑ k ∈ Finset.Icc (n + 2) (4 * p), sc k * ∑ α, Y α k with htail
  have hY0 : ∀ α k, 0 ≤ Y α k := fun α k => (norm_nonneg _).trans (hY α k)
  have htail0 : 0 ≤ tail :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hsc0 k) (Finset.sum_nonneg fun α _ => hY0 α k)
  have hQp : Q ^ (4 * p - n) ≤ Q ^ (4 * p) := pow_le_pow_right₀ hQ1 (Nat.sub_le _ _)
  have hQ0 : 0 ≤ Q ^ (4 * p) := by positivity
  -- the decomposition
  have hdec : ∑ α, s α * x α n = ∑ α, s α * y α n + ∑ α, s α * (x α n - y α n + r α n) -
      ∑ α, s α * r α n := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hn1 : ‖∑ α, s α * (x α n - y α n + r α n)‖ ≤ ∑ α, ‖x α n - y α n + r α n‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hs α)
  have hn2 : ‖∑ α, s α * r α n‖ ≤ ∑ α, ‖r α n‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hs α)
  have hT : ∑ α, ∑ k ∈ Finset.Icc (n + 2) (4 * p), sc k * (‖y α k‖ + ‖r α k‖) ≤
      tail + 4 * p * (2 * E) := by
    rw [Finset.sum_comm]
    have hk : ∀ k ∈ Finset.Icc (n + 2) (4 * p), ∑ α, sc k * (‖y α k‖ + ‖r α k‖) ≤
        sc k * ∑ α, Y α k + 2 * E := by
      intro k hk
      have hk4 : k ≤ 4 * p := (Finset.mem_Icc.1 hk).2
      rw [← Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => hY α k)
        (hsc0 k)) (hE k hk4)
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc (n + 2) (4 * p)).card : ℝ) ≤ 4 * p := by
      rw [Nat.card_Icc]
      have : 4 * p + 1 - (n + 2) ≤ 4 * p := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hcard (by linarith : (0 : ℝ) ≤ 2 * E)
    linarith
  have hsum : sc n * ∑ α, ‖x α n - y α n + r α n‖ ≤ Q ^ (4 * p) * (tail + 4 * p * (2 * E)) := by
    rw [Finset.mul_sum]
    calc ∑ α, sc n * ‖x α n - y α n + r α n‖
        ≤ ∑ α, Q ^ (4 * p) * ∑ k ∈ Finset.Icc (n + 2) (4 * p), sc k * (‖y α k‖ + ‖r α k‖) := by
          refine Finset.sum_le_sum fun α _ => (hchain α).trans ?_
          exact mul_le_mul_of_nonneg_right hQp
            (Finset.sum_nonneg fun k _ => mul_nonneg (hsc0 k) (by positivity))
      _ = Q ^ (4 * p) * ∑ α, ∑ k ∈ Finset.Icc (n + 2) (4 * p), sc k * (‖y α k‖ + ‖r α k‖) := by
          rw [Finset.mul_sum]
      _ ≤ Q ^ (4 * p) * (tail + 4 * p * (2 * E)) := mul_le_mul_of_nonneg_left hT hQ0
  have hrn := hE n hn4
  have hmain : sc n * ‖∑ α, s α * x α n‖ ≤ B + Q ^ (4 * p) * (tail + 4 * p * (2 * E)) + 2 * E := by
    rw [hdec]
    calc sc n * ‖∑ α, s α * y α n + ∑ α, s α * (x α n - y α n + r α n) - ∑ α, s α * r α n‖
        ≤ sc n * (‖∑ α, s α * y α n‖ + ∑ α, ‖x α n - y α n + r α n‖ + ∑ α, ‖r α n‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (hsc0 n)
          refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add le_rfl hn1)) hn2)
      _ = sc n * ‖∑ α, s α * y α n‖ + sc n * ∑ α, ‖x α n - y α n + r α n‖ +
            sc n * ∑ α, ‖r α n‖ := by ring
      _ ≤ B + Q ^ (4 * p) * (tail + 4 * p * (2 * E)) + 2 * E :=
          add_le_add (add_le_add hB hsum) hrn
  refine hmain.trans ?_
  have hQ1' : 1 ≤ Q ^ (4 * p) := one_le_pow₀ hQ1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith [mul_nonneg hQ0 htail0, mul_nonneg hQ0 hE0, mul_nonneg hQ0 hB0,
    mul_nonneg (mul_nonneg hQ0 hE0) hp0, mul_nonneg (mul_nonneg hQ0 hB0) hp0,
    mul_nonneg (mul_nonneg hQ0 htail0) hp0]

/-- `τ/N ≤ Ψ^W` on `𝐃^W(τ, N)`. -/
private lemma taylor_psi_ge {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (a : Fin N → ℝ) {z : ℂ}
    (hz : z ∈ domW τ N) : τ / N ≤ PsiW a z := by
  obtain ⟨h0, -, -, hη⟩ := hz
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  unfold PsiW
  linarith [Real.sqrt_nonneg ((mW a z).im / (N * z.im))]

/-! ## Lemma 7.16 for deformed Wigner matrices -/

/-- Lemma 7.16 analogue: the coefficients at `W^{(ij),0}` are bounded by those at `W`. -/
theorem wig_zero_to_theta (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (P : ModelClassW N) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N C P A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
        ∀ (s : UpperIdx N → ℂ) (n : ℕ) (B : ℝ), (∀ α, ‖s α‖ ≤ 1) → 0 ≤ B → 2 ≤ n → n ≤ 4 * p →
          ((N : ℝ) ^ (-(n : ℝ) / 2) *
            ‖∑ α : UpperIdx N, s α * ∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n‖
              ≤ B) →
          (N : ℝ) ^ (-(n : ℝ) / 2) * ‖∑ α : UpperIdx N, (s α : ℂ) *
            ∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) n‖ ≤
            K * (B + (N : ℝ) ^ δ * PsiW (specOf A) z ^ p
              + ∑ k ∈ Finset.Icc (n + 2) (4 * p), (N : ℝ) ^ (-(k : ℝ) / 2) *
                ∑ α : UpperIdx N, ∫ ω, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) k‖) := by
  have _hpEven := hp
  have hδ1 : δ ≤ 1 / 120 := by nlinarith
  set L : ℝ := taylorL C p with hLdef
  have hL0 : 0 ≤ L := taylorL_nonneg C p
  set Q : ℝ := 1 + 8 * p * L with hQ
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) ≤ 8 * p * L := by positivity
    linarith
  refine ⟨(3 + 8 * p) * Q ^ (4 * p), by positivity, ?_⟩
  obtain ⟨N₁, h₁⟩ := wig_rough_bound τ C C₀ δ (δ / 4) (dPrev p) hτ hτ1 hδ hC₀ hC₀δ (by positivity)
  obtain ⟨N₂, h₂⟩ := taylor_markov C (δ / 4) (dPrev p) (by positivity)
  set K36 : ℝ := 36 * (1 + τ⁻¹) with hK36
  have hK360 : 0 ≤ K36 := by positivity
  refine ⟨max (max (max N₁ N₂) (max 2 ⌈τ⁻¹⌉₊))
    (max (max ⌈K36 ^ (1 / 4 : ℝ)⁻¹⌉₊ ⌈taylorK1 τ p ^ (1 / 10 : ℝ)⁻¹⌉₊) ⌈taylorKM p C⌉₊), ?_⟩
  intro N hN A S P m hset hm hPA Ω _ _ W hW hP z hz v hv s n B hs hB0 hn2 hn4 hBhyp
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have h36N : ⌈K36 ^ (1 / 4 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hK1N : ⌈taylorK1 τ p ^ (1 / 10 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hKMN : ⌈taylorKM p C⌉₊ ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have h36 : K36 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := taylor_le_rpow hK360 (by norm_num) h36N
  have hK1 : taylorK1 τ p ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    taylor_le_rpow (taylorK1_nonneg hτ p) (by norm_num) hK1N
  have hKM : taylorKM p C ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hKMN)
  -- the point `z`
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  obtain ⟨hη0, -, hηl, -⟩ := id hzD
  have hηN : z.im⁻¹ ≤ N := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ z.im :=
      (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)).trans hηl
    rw [Real.rpow_neg_one] at h1
    exact (inv_le_comm₀ hη0 hNp).2 h1
  have hPi : ∀ x y : Fin N → ℝ, ‖ent (piW A z) x y‖ ≤ τ⁻¹ * testNorm x * testNorm y :=
    fun x y => norm_piW_le hτ hset.symmA hset.standing hzS x y
  have hPv : ‖ent (piW A z) v v‖ ≤ τ⁻¹ := by
    have := hPi v v
    rwa [hv, mul_one, mul_one] at this
  have hΨ : τ / N ≤ PsiW (specOf A) z := taylor_psi_ge hN1 hτ _ hzD
  have hr1 := (h₁ N hNN₁ A S P m hset hm hPA Ω W hW hP z hz).1
  -- the per-entry data
  set Γ : ℕ → ℝ := fun l => τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) with hΓdef
  have hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ dPrev p - 5 := by
    unfold dPrev
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    push_cast
    nlinarith
  have hτge : (N : ℝ)⁻¹ ≤ τ := by
    rw [inv_le_comm₀ hNp hτ]; exact hτN
  have hΓ : ∀ l : ℕ, (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ Γ l := by
    intro l
    have h1 : ((N : ℝ)⁻¹) ^ p ≤ τ ^ p := pow_le_pow_left₀ (by positivity) hτge p
    have h2 : (N : ℝ) ^ (-2 - (p : ℝ)) ≤ (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by have := (Nat.cast_nonneg l : (0 : ℝ) ≤ l); linarith)
    have h3 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ ((N : ℝ)⁻¹) ^ p * (N : ℝ) ^ (-2 - (p : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
      refine Real.rpow_le_rpow_of_exponent_le hN1r ?_
      have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      push_cast
      linarith
    calc (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ ((N : ℝ)⁻¹) ^ p * (N : ℝ) ^ (-2 - (p : ℝ)) := h3
      _ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hNp.le _) (by positivity)
  have hexp : ∀ (α : UpperIdx N) (l : ℕ), l ≤ 4 * p →
      (∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) l) =
        (∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
          (∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ k) *
          (∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) (l + k))) +
          ∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l ∧
      ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤ 2 * (N : ℝ) ^ δ * Γ l := by
    intro α l hl
    have hξ := h₂ N hNN₂ (fun ω => W ω α.1.1 α.1.2)
      (fun q => ⟨hW.integrable_moment q _ _, hW.moment q _ _⟩)
    have hev := taylor_event hN2 hτ hδ hδ1 hp2 h36 hK1 hset.symmA hη0 hv hPi hW.symm hr1
      α.1.1 α.1.2 hξ l hl
    exact taylor_expect hN1 hset.symmA hη0 hηN hv hPv hτN hW α p l hl hδ.le hD (hΓ l) hKM hev
  -- moments of the entries
  have hμ0 : ∀ α : UpperIdx N, ∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ 0 = 1 := by
    intro α; simp
  have hμ1 : ∀ α : UpperIdx N, ∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ 1 = 0 := by
    intro α
    simp only [pow_one]
    rw [integral_complex_ofReal, hW.mean]
    simp
  have hμ : ∀ (α : UpperIdx N) (k : ℕ), ‖∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ k‖ ≤
      (N : ℝ) ^ (-(k : ℝ) / 2) * max (C k) 0 :=
    fun α k => taylor_moment_entry hW hN1 _ _ k
  -- the recursion for every entry
  have hchain : ∀ α : UpperIdx N, (N : ℝ) ^ (-(n : ℝ) / 2) *
      ‖(∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) n) -
        (∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) n) +
        ∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p n‖ ≤
      Q ^ (4 * p - n) * ∑ k ∈ Finset.Icc (n + 2) (4 * p), (N : ℝ) ^ (-(k : ℝ) / 2) *
        (‖∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) k‖ +
          ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p k‖) := by
    intro α
    exact taylor_chain hN1 p
      (fun l => ∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) l)
      (fun l => ∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) l)
      (fun l => ∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l)
      (fun k => ∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ k) (fun k => max (C k) 0) hL0
      (fun l hl => (hexp α l hl).1) (hμ0 α) (hμ1 α) (hμ α) (fun l k h => taylorL_ge h) n hn4
  -- the remainders summed over the entries
  have hcard : (Fintype.card (UpperIdx N) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h := Fintype.card_subtype_le (fun q : Fin N × Fin N => q.1 ≤ q.2)
    rw [Fintype.card_prod, Fintype.card_fin] at h
    have : (Fintype.card (UpperIdx N) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h
    rw [sq]; push_cast at this; exact this
  have hE : ∀ l ≤ 4 * p, (N : ℝ) ^ (-(l : ℝ) / 2) *
      ∑ α : UpperIdx N, ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤
        2 * ((N : ℝ) ^ δ * PsiW (specOf A) z ^ p) := by
    intro l hl
    have h1 : ∑ α : UpperIdx N, ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤
        (N : ℝ) ^ 2 * (2 * (N : ℝ) ^ δ * Γ l) := by
      calc ∑ α : UpperIdx N, ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l‖
          ≤ ∑ _α : UpperIdx N, 2 * (N : ℝ) ^ δ * Γ l :=
            Finset.sum_le_sum fun α _ => (hexp α l hl).2
        _ = (Fintype.card (UpperIdx N) : ℝ) * (2 * (N : ℝ) ^ δ * Γ l) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (N : ℝ) ^ 2 * (2 * (N : ℝ) ^ δ * Γ l) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
    have h2 : (N : ℝ) ^ (-(l : ℝ) / 2) * ((N : ℝ) ^ 2 * Γ l) = (τ / N) ^ p := by
      simp only [hΓdef]
      rw [div_pow, show (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      rw [show (N : ℝ) ^ (-(l : ℝ) / 2) * ((N : ℝ) ^ ((2 : ℕ) : ℝ) *
          (τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p))) =
          τ ^ p * ((N : ℝ) ^ (-(l : ℝ) / 2) * (N : ℝ) ^ ((2 : ℕ) : ℝ) *
            (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p)) by ring,
        ← Real.rpow_add hNp, ← Real.rpow_add hNp]
      rw [show -(l : ℝ) / 2 + ((2 : ℕ) : ℝ) + ((l : ℝ) / 2 - 2 - p) = -(p : ℝ) by push_cast; ring,
        Real.rpow_neg hNp.le, Real.rpow_natCast]
      ring
    have h3 : (τ / N) ^ p ≤ PsiW (specOf A) z ^ p := pow_le_pow_left₀ (by positivity) hΨ p
    calc (N : ℝ) ^ (-(l : ℝ) / 2) *
          ∑ α : UpperIdx N, ‖∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l‖
        ≤ (N : ℝ) ^ (-(l : ℝ) / 2) * ((N : ℝ) ^ 2 * (2 * (N : ℝ) ^ δ * Γ l)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hNp.le _)
      _ = 2 * (N : ℝ) ^ δ * ((N : ℝ) ^ (-(l : ℝ) / 2) * ((N : ℝ) ^ 2 * Γ l)) := by ring
      _ = 2 * (N : ℝ) ^ δ * (τ / N) ^ p := by rw [h2]
      _ ≤ 2 * (N : ℝ) ^ δ * PsiW (specOf A) z ^ p :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * ((N : ℝ) ^ δ * PsiW (specOf A) z ^ p) := by ring
  have hE0 : 0 ≤ (N : ℝ) ^ δ * PsiW (specOf A) z ^ p := by
    have : 0 ≤ PsiW (specOf A) z := le_trans (by positivity) hΨ
    positivity
  have h := taylor_assemble hN1 p n hn4 s hs
    (fun α l => ∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) l)
    (fun α l => ∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) l)
    (fun α l => ∫ ω, taylorRem A (W ω) z v α.1.1 α.1.2 p l)
    (fun α k => ∫ ω, ‖fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) k‖)
    (fun α k => norm_integral_le_integral_norm _) hQ1 hBhyp hB0 hE0 hE hchain
  exact h

#print axioms Anisotropic.wig_zero_to_theta

end Anisotropic
