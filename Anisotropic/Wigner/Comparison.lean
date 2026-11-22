module

public import Anisotropic.Comparison.Gronwall
public import Anisotropic.Comparison.Interpolation
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.Diag
public import Anisotropic.Wigner.GOE
public import Anisotropic.Wigner.HighOrder
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.Props
public import Anisotropic.Wigner.Taylor
public import Anisotropic.Wigner.Third

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # From (A_m) to (C_m): the comparison induction -/

/-! ## The spectral form of `G^W` and invertibility -/

/-- A real symmetric `M` is `U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma cmp_eig_decomp {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
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
private lemma cmp_right_inv {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
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
private lemma cmp_isUnit_det {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : IsUnit (cplx M - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  obtain ⟨U, l, hUU, hUU', hMU⟩ := cmp_eig_decomp hM
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  exact Matrix.isUnit_det_of_right_inverse (cmp_right_inv hUU hUU' hMU hne)

/-! ## Updates of a symmetric matrix -/

/-- The update of a symmetric matrix is symmetric. -/
private lemma cmp_Wupd_symm {N : ℕ} {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
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
private lemma cmp_Wupd_self {N : ℕ} {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm)
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
private lemma cmp_herm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) (i j : Fin N) (t : ℝ) : (Wupd Wm i j t + A).IsHermitian := by
  have hW' : (Wupd Wm i j t).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact cmp_Wupd_symm hW i j t
  exact hW'.add hA

/-- `H(y) − H(x) = (y − x) Δ` for `H(t) = W^{(ij),t} + A − z`. -/
private lemma cmp_H_sub {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N)
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
private lemma cmp_res_id {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x y : ℝ) :
    GW A (Wupd Wm i j y) z - GW A (Wupd Wm i j x) z =
      (-((y - x : ℝ) : ℂ)) • (GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j y) z) := by
  set Hx := cplx (Wupd Wm i j x + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hHx
  set Hy := cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ) with hHy
  have hx : IsUnit Hx.det := cmp_isUnit_det (cmp_herm hA hW i j x) hz
  have hy : IsUnit Hy.det := cmp_isUnit_det (cmp_herm hA hW i j y) hz
  have e1 : Hx⁻¹ * Hx = 1 := Matrix.nonsing_inv_mul _ hx
  have e2 : Hy * Hy⁻¹ = 1 := Matrix.mul_nonsing_inv _ hy
  have hs := cmp_H_sub A Wm z i j x y
  change Hy⁻¹ - Hx⁻¹ = (-((y - x : ℝ) : ℂ)) • (Hx⁻¹ * deltaW i j * Hy⁻¹)
  have key : Hx⁻¹ * (Hx - Hy) * Hy⁻¹ = Hy⁻¹ - Hx⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [← key, show Hx - Hy = -(Hy - Hx) by abel, hs, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, neg_smul]

/-! ## Derivatives along the entry `(i, j)` -/

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def CmpMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private lemma cmp_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : CmpMD f f' x) (hg : CmpMD g g' x) :
    CmpMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private lemma cmp_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    CmpMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

private lemma cmp_ent_eq {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ent B x y = ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := by
  simp only [ent, cvec, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private lemma cmp_MD_ent {ι : Type*} [Fintype ι] {f : ℝ → Matrix ι ι ℂ}
    {f' : Matrix ι ι ℂ} {x : ℝ} (hf : CmpMD f f' x) (a b : ι → ℝ) :
    HasDerivAt (fun y => ent (f y) a b) (ent f' a b) x := by
  simp only [cmp_ent_eq]
  exact HasDerivAt.fun_sum fun s _ => HasDerivAt.fun_sum fun t _ =>
    ((hf s t).const_mul _).mul_const _

/-- `y ↦ G(W^{(ij),y})` is continuous. -/
private lemma cmp_continuousAt_G {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
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
  have hu := cmp_isUnit_det (cmp_herm hA hW i j x) hz
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  exact hinv.comp (f := fun y => cplx (Wupd Wm i j y + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ))
    hX.continuousAt

/-- `d/dy G(W^{(ij),y}) = −G Δ G`. -/
private lemma cmp_MD_G {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) :
    CmpMD (fun y => GW A (Wupd Wm i j y) z)
      (-(GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j x) z)) x := by
  intro s t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set G0 := GW A (Wupd Wm i j x) z with hG0
  have hid : ∀ h : ℝ, GW A (Wupd Wm i j (x + h)) z - G0 =
      (-(h : ℂ)) • (G0 * deltaW i j * GW A (Wupd Wm i j (x + h)) z) := by
    intro h
    have e := cmp_res_id hA hW hz i j x (x + h)
    rw [show x + h - x = h by ring] at e
    exact e
  have hc : ∀ r, ContinuousAt (fun h : ℝ => GW A (Wupd Wm i j (x + h)) z r t) 0 := fun r => by
    have h2 : ContinuousAt (fun h : ℝ => x + h) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have h3 : ContinuousAt ((fun y => GW A (Wupd Wm i j y) z) ∘ fun h : ℝ => x + h) 0 :=
      ContinuousAt.comp_of_eq (cmp_continuousAt_G hA hW hz i j x) h2 (by simp)
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
private lemma cmp_MD_pow {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    CmpMD (fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-(k : ℂ) • (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using cmp_MD_const (1 : Matrix (Fin N) (Fin N) ℂ) x
  | succ k ih =>
    have hDG := cmp_MD_mul (cmp_MD_const (deltaW i j) x) (cmp_MD_G hA hW hz i j x)
    have h := cmp_MD_mul ih hDG
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
private lemma cmp_MD_T {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    CmpMD (fun y => GW A (Wupd Wm i j y) z * (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-((k : ℂ) + 1) • (GW A (Wupd Wm i j x) z *
        (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1))) x := by
  have h := cmp_MD_mul (cmp_MD_G hA hW hz i j x) (cmp_MD_pow hA hW hz i j x k)
  convert h using 1
  rw [Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_assoc (GW A (Wupd Wm i j x) z) (deltaW i j),
    Matrix.mul_assoc (GW A (Wupd Wm i j x) z), ← pow_succ', neg_add, add_smul, neg_one_smul,
    add_comm]

/-- `d/dx a_k(x) = (k + 1) a_{k+1}(x)` along the entry `(i, j)` of a symmetric matrix. -/
private lemma cmp_hasDerivAt_resCoeffW {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i j : Fin N)
    (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => resCoeffW A (Wupd Wm i j y) z v i j k)
      (((k : ℂ) + 1) * resCoeffW A (Wupd Wm i j x) z v i j (k + 1)) x := by
  have hT := cmp_MD_T hA hW hz i j x k
  have hC : CmpMD (fun y => GW A (Wupd Wm i j y) z * (deltaW i j * GW A (Wupd Wm i j y) z) ^ k
      - if k = 0 then piW A z else 0)
      (-((k : ℂ) + 1) • (GW A (Wupd Wm i j x) z *
        (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1))) x := by
    intro s t
    simpa using (hT s t).sub_const ((if k = 0 then piW A z else 0) s t)
  have h := (cmp_MD_ent hC v v).const_mul ((-1 : ℂ) ^ k)
  refine h.congr_deriv ?_
  have hs : ∀ (c : ℂ) (B : Matrix (Fin N) (Fin N) ℂ), ent (c • B) v v = c * ent B v v := by
    intro c B
    simp [ent, smul_mulVec, dotProduct_smul]
  simp only [resCoeffW, hs, Nat.succ_ne_zero, ↓reduceIte, sub_zero, pow_succ]
  ring

/-! ## Measurability -/

/-- `W ↦ G^W(z)` is measurable. -/
private lemma cmp_measurable_G {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
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
private lemma cmp_continuous_ent {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Continuous fun B : Matrix ι ι ℂ => ent B x y := by
  have : (fun B : Matrix ι ι ℂ => ent B x y) =
      fun B => ∑ s, ∑ t, (x s : ℂ) * B s t * (y t : ℂ) := funext fun B => cmp_ent_eq B x y
  rw [this]
  exact continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ =>
    (continuous_const.mul (continuous_id.matrix_elem s t)).mul continuous_const

/-- `W ↦ a_k(W)` is measurable. -/
private lemma cmp_measurable_res {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (k : ℕ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => resCoeffW A Wm z v i j k := by
  have hc : Continuous fun X : Matrix (Fin N) (Fin N) ℂ =>
      (-1 : ℂ) ^ k * ent (X * (deltaW i j * X) ^ k - if k = 0 then piW A z else 0) v v :=
    continuous_const.mul ((cmp_continuous_ent v v).comp
      ((continuous_id.matrix_mul ((continuous_const.matrix_mul continuous_id).pow k)).sub
        continuous_const))
  exact hc.measurable.comp (cmp_measurable_G A z)

/-- `x ↦ f_n(a(x))` is measurable when every `x ↦ a_k(x)` is. -/
private lemma cmp_measurable_fCoeff {X : Type*} [MeasurableSpace X] (p n : ℕ)
    {a : X → ℕ → ℂ} (ha : ∀ k, Measurable fun x => a x k) :
    Measurable fun x => fCoeff p (a x) n := by
  unfold fCoeff
  refine Finset.measurable_sum _ fun κ _ => Finset.measurable_prod _ fun r _ => ?_
  split_ifs
  · exact ha _
  · exact Complex.continuous_conj.measurable.comp (ha _)

/-- `(W, t) ↦ W^{(ij),t}` is continuous. -/
private lemma cmp_continuous_Wupd {N : ℕ} (i j : Fin N) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => Wupd q.1 i j q.2 := by
  refine continuous_pi fun s => continuous_pi fun u => ?_
  simp only [Wupd]
  split_ifs
  · exact continuous_snd
  · exact continuous_fst.matrix_elem s u

/-- `W ↦ f_n(a(W^{(ij),t}))` is measurable. -/
private lemma cmp_measurable_fUpd {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (p n : ℕ) (t : ℝ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ =>
      fCoeff p (resCoeffW A (Wupd Wm i j t) z v i j) n :=
  cmp_measurable_fCoeff p n fun k => (cmp_measurable_res A z v i j k).comp
    ((cmp_continuous_Wupd i j).measurable.comp (measurable_id.prodMk measurable_const))

/-! ## Deterministic bounds on the coefficients -/

/-- The elementary matrix `E_{ab}`. -/
private def cmpE {N : ℕ} (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun s u => if s = a ∧ u = b then 1 else 0

private lemma cmp_ent_add {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X + Y) x y = ent X x y + ent Y x y := by
  simp [ent, add_mulVec, dotProduct_add]

private lemma cmp_ent_sub {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (X - Y) x y = ent X x y - ent Y x y := by
  simp [ent, Matrix.sub_mulVec, dotProduct_sub]

private lemma cmp_ent_smul {N : ℕ} (c : ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℝ) :
    ent (c • X) x y = c * ent X x y := by
  simp [ent, smul_mulVec, dotProduct_smul]

/-- `⟨x, X E_{ab} Y y⟩ = ⟨x, X e_a⟩ ⟨e_b, Y y⟩`. -/
private lemma cmp_ent_single {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N)
    (x y : Fin N → ℝ) : ent (X * cmpE a b * Y) x y = ent X x (eI a) * ent Y (eI b) y := by
  have h1 : ∀ s u, (X * cmpE a b) s u = if u = b then X s a else 0 := by
    intro s u
    simp only [Matrix.mul_apply, cmpE, Matrix.of_apply]
    by_cases hu : u = b
    · subst hu
      simp
    · simp [hu]
  have h2 : X * cmpE a b * Y = fun s t => X s a * Y b t := by
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

private lemma cmp_deltaW_ne {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    deltaW i j = cmpE i j + cmpE j i := by
  ext s u
  simp only [deltaW, cmpE, Matrix.add_apply, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all

private lemma cmp_deltaW_eq {N : ℕ} (i : Fin N) : deltaW i i = cmpE i i := by
  ext s u
  simp [deltaW, cmpE]

/-- `|⟨x, X Δ Y y⟩| ≤ |⟨x, X e_i⟩||⟨e_j, Y y⟩| + |⟨x, X e_j⟩||⟨e_i, Y y⟩|`. -/
private lemma cmp_ent_delta_le {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (x y : Fin N → ℝ) :
    ‖ent (X * deltaW i j * Y) x y‖ ≤ ‖ent X x (eI i)‖ * ‖ent Y (eI j) y‖ +
      ‖ent X x (eI j)‖ * ‖ent Y (eI i) y‖ := by
  by_cases h : i = j
  · subst h
    rw [cmp_deltaW_eq, cmp_ent_single, norm_mul]
    exact le_add_of_nonneg_right (by positivity)
  · rw [cmp_deltaW_ne h, Matrix.mul_add, Matrix.add_mul, cmp_ent_add, cmp_ent_single,
      cmp_ent_single]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]

/-- The word bound: if `|G_{xy}| ≤ b` for `x, y ∈ {u₀, e_i, e_j}`, then
`|(G (Δ G)^k)_{xy}| ≤ (2b)^k b`. -/
private lemma cmp_word_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
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
    refine (cmp_ent_delta_le _ _ i j _ _).trans ?_
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
private lemma cmp_res_le {N : ℕ} (A M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) (u : Fin 3 → Fin N → ℝ) (hu0 : u 0 = v) (hu1 : u 1 = eI i) (hu2 : u 2 = eI j)
    {b t : ℝ} (hb : ∀ a c, ‖ent (GW A M z) (u a) (u c)‖ ≤ b) (ht : ‖ent (piW A z) v v‖ ≤ t)
    (k : ℕ) : ‖resCoeffW A M z v i j k‖ ≤ (2 * b + t + 1) ^ (k + 1) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  have hw := cmp_word_le (GW A M z) i j u hu1 hu2 hb k 0 0
  rw [hu0] at hw
  have hc : ‖ent (if k = 0 then piW A z else 0) v v‖ ≤ t := by
    split_ifs
    · exact ht
    · simpa [ent] using ht0
  have h1 : ‖resCoeffW A M z v i j k‖ ≤ (2 * b) ^ k * b + t := by
    unfold resCoeffW
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, cmp_ent_sub]
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

/-- `|f_n| ≤ (n + 1)^p (2b + t + 1)^{n+p}` under the hypotheses of `cmp_res_le`. -/
private lemma cmp_f_le {N : ℕ} (A M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) (u : Fin 3 → Fin N → ℝ) (hu0 : u 0 = v) (hu1 : u 1 = eI i) (hu2 : u 2 = eI j)
    {b t : ℝ} (hb : ∀ a c, ‖ent (GW A M z) (u a) (u c)‖ ≤ b) (ht : ‖ent (piW A z) v v‖ ≤ t)
    (p n : ℕ) :
    ‖fCoeff p (resCoeffW A M z v i j) n‖ ≤ ((n : ℝ) + 1) ^ p * (2 * b + t + 1) ^ (n + p) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  exact norm_fCoeff_le p (by linarith) n fun k _ =>
    cmp_res_le A M z v i j u hu0 hu1 hu2 hb ht k

/-- The 2×2 perturbation: if `|G_{xy}(W)| ≤ g` on `{u₀, e_i, e_j}` and `18|s − W_{ij}| g ≤ 1`, then
`|G_{xy}(W^{(ij),s})| ≤ 18 g` there. -/
private lemma cmp_pert {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (u : Fin 3 → Fin N → ℝ)
    (hu1 : u 1 = eI i) (hu2 : u 2 = eI j) {g : ℝ} (hg : ∀ a c, ‖ent (GW A Wm z) (u a) (u c)‖ ≤ g)
    {s : ℝ} (hs : 18 * |s - Wm i j| * g ≤ 1) :
    ∀ a c, ‖ent (GW A (Wupd Wm i j s) z) (u a) (u c)‖ ≤ 18 * g := by
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg 0 0)
  have hid := cmp_res_id hA hW hz i j (Wm i j) s
  rw [cmp_Wupd_self hW] at hid
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
      rw [cmp_ent_add, cmp_ent_smul]
    have hD := cmp_ent_delta_le G Gs i j (u a) (u c)
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

private lemma cmp_testNorm_orth {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (v : Fin N → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

private lemma cmp_ent_sandwich {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
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
private lemma cmp_ent_le {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (x y : Fin N → ℝ) :
    ‖ent (GW A Wm z) x y‖ ≤ z.im⁻¹ * testNorm x * testNorm y := by
  have hW' : Wm.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hW
  obtain ⟨U, l, hUU, hUU', hMU⟩ := cmp_eig_decomp (hW'.add hA)
  have hne : ∀ k, (l k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((l k : ℂ) - z)⁻¹) * (cplx U)ᵀ :=
    Matrix.inv_eq_right_inv (cmp_right_inv hUU hUU' hMU hne)
  have hsq : ∀ v : Fin N → ℝ, ∑ k, (Uᵀ *ᵥ v) k ^ 2 = testNorm v ^ 2 := by
    intro v
    rw [← cmp_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v]
    unfold testNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [hG, cmp_ent_sandwich]
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

private lemma cmp_testNorm_eI {N : ℕ} (i : Fin N) : testNorm (eI i) = 1 := by
  simp [testNorm, eI, Pi.single_apply]

/-- The test vectors `(v, e_i, e_j)`. -/
private def cmpU {N : ℕ} (v : Fin N → ℝ) (i j : Fin N) : Fin 3 → Fin N → ℝ := ![v, eI i, eI j]

private lemma cmpU_testNorm {N : ℕ} {v : Fin N → ℝ} (hv : testNorm v = 1) (i j : Fin N)
    (a : Fin 3) : testNorm (cmpU v i j a) = 1 := by
  fin_cases a <;> simp [cmpU, hv, cmp_testNorm_eI]

/-! ## The remainder of the re-expansion -/

/-- `R_l = f_l(W) − ∑_{k ≤ 4p−l} C(l+k, l) W_{ij}^k f_{l+k}(W^{(ij),0})`. -/
private def cmpRem {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) (p l : ℕ) : ℂ :=
  fCoeff p (resCoeffW A Wm z v i j) l -
    ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) * ((Wm i j : ℝ) : ℂ) ^ k *
      fCoeff p (resCoeffW A (Wupd Wm i j 0) z v i j) (l + k)

private lemma cmp_measurable_rem {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (v : Fin N → ℝ) (i j : Fin N) (p l : ℕ) :
    Measurable fun Wm : Matrix (Fin N) (Fin N) ℝ => cmpRem A Wm z v i j p l := by
  unfold cmpRem
  refine (cmp_measurable_fCoeff p l fun k => cmp_measurable_res A z v i j k).sub ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  refine (measurable_const.mul ?_).mul (cmp_measurable_fUpd A z v i j p (l + k) 0)
  exact (Complex.measurable_ofReal.comp (measurable_pi_iff.1
    (measurable_pi_iff.1 measurable_id i) j)).pow_const k

private lemma cmp_abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
  rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- The remainder on the a priori event: `|G_{xy}| ≤ g` on `{v, e_i, e_j}`, `|Π_{vv}| ≤ t` and
`36 |W_{ij}| g ≤ 1` give `|R_l| ≤ (4p+1)! (4p+2)^p (36g + t + 1)^{5p+1} |W_{ij}|^{4p+1−l}`. -/
private lemma cmp_rem_good {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℝ) (i j : Fin N) {g t : ℝ}
    (hg : ∀ a c, ‖ent (GW A Wm z) (cmpU v i j a) (cmpU v i j c)‖ ≤ g)
    (ht : ‖ent (piW A z) v v‖ ≤ t) (hξ : 36 * |Wm i j| * g ≤ 1) (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖cmpRem A Wm z v i j p l‖ ≤ ((4 * p + 1).factorial : ℝ) *
      ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p * (2 * (18 * g) + t + 1) ^ (4 * p + 1 + p)) *
      |Wm i j| ^ (4 * p - l + 1) := by
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg 0 0)
  have ha : ∀ k x, HasDerivAt (fun y => resCoeffW A (Wupd Wm i j y) z v i j k)
      (((k : ℂ) + 1) * resCoeffW A (Wupd Wm i j x) z v i j (k + 1)) x :=
    fun k x => cmp_hasDerivAt_resCoeffW hA hW hz v i j k x
  have hidx : l + (4 * p - l) + 1 = 4 * p + 1 := by omega
  have hT := fCoeff_taylor p ha l (4 * p - l) 0 (Wm i j)
    ((((4 * p + 1 : ℕ) : ℝ) + 1) ^ p * (2 * (18 * g) + t + 1) ^ (4 * p + 1 + p)) (fun s hs => by
      rw [zero_add, hidx]
      have hs' := cmp_abs_le_of_mem_uIcc hs
      have hd : 18 * |s - Wm i j| * g ≤ 1 := by
        have : |s - Wm i j| ≤ 2 * |Wm i j| := by
          calc |s - Wm i j| ≤ |s| + |Wm i j| := abs_sub _ _
            _ ≤ 2 * |Wm i j| := by linarith
        nlinarith
      have hp := cmp_pert hA hW hz i j (cmpU v i j) (by simp [cmpU]) (by simp [cmpU])
        hg hd
      exact cmp_f_le A (Wupd Wm i j s) z v i j (cmpU v i j) (by simp [cmpU])
        (by simp [cmpU]) (by simp [cmpU]) hp ht p (4 * p + 1))
  rw [zero_add, hidx, cmp_Wupd_self hW] at hT
  exact hT

/-- `|f_n(W)| ≤ (4p+1)^p (4N)^{5p}` for `n ≤ 4p` and a symmetric `W`, when `η⁻¹, t ≤ N`. -/
private lemma cmp_f_det {N : ℕ} (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N)
    {v : Fin N → ℝ} (hv : testNorm v = 1) (i j : Fin N) {t : ℝ}
    (ht : ‖ent (piW A z) v v‖ ≤ t) (htN : t ≤ N) (p n : ℕ) (hn : n ≤ 4 * p) :
    ‖fCoeff p (resCoeffW A Wm z v i j) n‖ ≤ ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : ∀ a c, ‖ent (GW A Wm z) (cmpU v i j a) (cmpU v i j c)‖ ≤ z.im⁻¹ := by
    intro a c
    have h := cmp_ent_le hA hW hz (cmpU v i j a) (cmpU v i j c)
    rwa [cmpU_testNorm hv, cmpU_testNorm hv, mul_one, mul_one] at h
  have h := cmp_f_le A Wm z v i j (cmpU v i j) (by simp [cmpU]) (by simp [cmpU])
    (by simp [cmpU]) hb ht p n
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
private def cmpKR (p : ℕ) : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ p * (1 + (4 * p + 1) * 2 ^ (4 * p))

private lemma cmpKR_nonneg (p : ℕ) : 0 ≤ cmpKR p := by
  unfold cmpKR; positivity

/-- The deterministic remainder bound `|R_l| ≤ K (4N)^{5p} (1 + |W_{ij}|^{4p})`. -/
private lemma cmp_rem_det {N : ℕ} (hN : 1 ≤ N) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N)
    {v : Fin N → ℝ} (hv : testNorm v = 1) (i j : Fin N) {t : ℝ}
    (ht : ‖ent (piW A z) v v‖ ≤ t) (htN : t ≤ N) (p l : ℕ) (hl : l ≤ 4 * p) :
    ‖cmpRem A Wm z v i j p l‖ ≤ cmpKR p * (4 * N) ^ (5 * p) * (1 + |Wm i j| ^ (4 * p)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set F : ℝ := ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) with hF
  have hF0 : 0 ≤ F := by positivity
  set X : ℝ := |Wm i j| with hX
  have hX0 : 0 ≤ X := abs_nonneg _
  have hW0 := cmp_Wupd_symm hW i j 0
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
    have hf := cmp_f_det hN hA hW0 hz hηN hv i j ht htN p (l + k) (by omega)
    calc ((l + k).choose l : ℝ) * |Wm i j| ^ k *
          ‖fCoeff p (resCoeffW A (Wupd Wm i j 0) z v i j) (l + k)‖
        ≤ 2 ^ (4 * p) * (1 + X ^ (4 * p)) * F := by
          gcongr
      _ = 2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F) := by ring
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfl := cmp_f_det hN hA hW hz hηN hv i j ht htN p l hl
  have hcard : ((4 * p - l + 1 : ℕ) : ℝ) ≤ 4 * p + 1 := by
    have : 4 * p - l + 1 ≤ 4 * p + 1 := by omega
    exact_mod_cast this
  unfold cmpRem
  refine (norm_sub_le _ _).trans ?_
  have hA0 : 0 ≤ 2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F) := by positivity
  have hX1 : F ≤ (1 + X ^ (4 * p)) * F :=
    le_mul_of_one_le_left hF0 (by linarith [pow_nonneg hX0 (4 * p)])
  calc _ ≤ F + ((4 * p - l + 1 : ℕ) : ℝ) * (2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F)) :=
        add_le_add hfl hsum
    _ ≤ (1 + X ^ (4 * p)) * F + (4 * p + 1) * (2 ^ (4 * p) * ((1 + X ^ (4 * p)) * F)) := by
        gcongr
    _ = cmpKR p * (4 * N) ^ (5 * p) * (1 + X ^ (4 * p)) := by
        unfold cmpKR; rw [hF]; ring

/-! ## The entry `W_{ij}`: Markov, independence, moments -/

private lemma cmp_le_rpow {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) {N : ℕ}
    (hN : ⌈K ^ a⁻¹⌉₊ ≤ N) : K ≤ (N : ℝ) ^ a := by
  have h1 : K ^ a⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  calc K = (K ^ a⁻¹) ^ a := by rw [← Real.rpow_mul hK, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by positivity) h1 ha.le

/-- `|y| ≤ N^{ε − 1/2}` with probability `≥ 1 − N^{−D}`, from the moments of `√N y` (Markov). -/
private lemma cmp_markov (C : ℕ → ℝ) (ε D : ℝ) (hε : 0 < ε) :
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
    cmp_le_rpow (zero_le_one.trans (le_max_right _ _)) (by positivity)
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
private lemma cmp_indep {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
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

/-! ## Expectations: the re-expansion and Lemma 7.7 -/

/-- The moment constant `2 K_R² 4^{10p} (1 + max(C_{8p}, 0))`. -/
private def cmpKM (p : ℕ) (C : ℕ → ℝ) : ℝ :=
  2 * cmpKR p ^ 2 * 4 ^ (10 * p) * (1 + max (C (8 * p)) 0)

/-- Expectation of the re-expansion along `α = (i, j)`: by independence of `W_{ij}` and
`W^{(ij),0}`, `E f_l(W) = ∑_k C(l+k, l) E W_{ij}^k E f_{l+k}(W^{(ij),0}) + E R_l`; Lemma 7.7 bounds
`|E R_l| ≤ 2 N^δ Γ` on the event `|R_l| ≤ Γ`. -/
private lemma cmp_expect {N : ℕ} (hN : 1 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (hηN : z.im⁻¹ ≤ N) {v : Fin N → ℝ}
    (hv : testNorm v = 1) {t : ℝ} (ht : ‖ent (piW A z) v v‖ ≤ t) (htN : t ≤ N) {C : ℕ → ℝ}
    {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N)
    (p l : ℕ) (hl : l ≤ 4 * p) {δ D Γ : ℝ} (hδ : 0 ≤ δ) (hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ D)
    (hΓ : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤ Γ) (hK : cmpKM p C ≤ N)
    (hev : HighProbAt N D {ω | ‖cmpRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤ Γ}) :
    (∫ ω, fCoeff p (resCoeffW A (W ω) z v α.1.1 α.1.2) l) =
      (∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
        (∫ ω, (W ω α.1.1 α.1.2 : ℂ) ^ k) *
        (∫ ω, fCoeff p (resCoeffW A (Wupd (W ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) (l + k))) +
        ∫ ω, cmpRem A (W ω) z v α.1.1 α.1.2 p l ∧
    ‖∫ ω, cmpRem A (W ω) z v α.1.1 α.1.2 p l‖ ≤ 2 * (N : ℝ) ^ δ * Γ := by
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
    fun n => ((cmp_measurable_fUpd A z v i j p n 0).comp hWm).aestronglyMeasurable
  have hFm : AEStronglyMeasurable fun ω => fCoeff p (resCoeffW A (W ω) z v i j) l :=
    ((cmp_measurable_fCoeff p l fun k => cmp_measurable_res A z v i j k).comp
      hWm).aestronglyMeasurable
  have hF0b : ∀ n ≤ 4 * p, ∀ ω, ‖fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) n‖ ≤ F0 :=
    fun n hn ω => cmp_f_det hN hA (cmp_Wupd_symm (hW.symm ω) i j 0) hz hηN hv i j ht htN p
      n hn
  have hFb : ∀ ω, ‖fCoeff p (resCoeffW A (W ω) z v i j) l‖ ≤ F0 :=
    fun ω => cmp_f_det hN hA (hW.symm ω) hz hηN hv i j ht htN p l hl
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
    fun k => ((cmp_indep hW α).symm.comp (hpowm k)
      (cmp_measurable_fCoeff p (l + k) fun k' =>
        cmp_measurable_res A z v i j k')).integral_fun_mul_eq_mul_integral
      (hym' k) (hF0m (l + k))
  set Rf : Ω → ℂ := fun ω => cmpRem A (W ω) z v i j p l with hRf
  set Sf : Ω → ℂ := fun ω => ∑ k ∈ Finset.range (4 * p - l + 1), ((l + k).choose l : ℂ) *
      ((W ω i j : ℂ) ^ k * fCoeff p (resCoeffW A (Wupd (W ω) i j 0) z v i j) (l + k)) with hSf
  have hSi : Integrable Sf := integrable_finsetSum _ fun k hk => (hprodi k hk).const_mul _
  have hdec : ∀ ω, fCoeff p (resCoeffW A (W ω) z v i j) l = Sf ω + Rf ω := by
    intro ω
    simp only [hSf, hRf, cmpRem]
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
    set KR := cmpKR p with hKR
    have hKR0 : 0 ≤ KR := cmpKR_nonneg p
    set Cr : ℝ := ((10 * p + 1 : ℕ) : ℝ) with hCr
    set C' : ℝ := max (C (8 * p)) 0 with hC'
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hRb : ∀ ω, ‖Rf ω‖ ≤ KR * (4 * N) ^ (5 * p) * (1 + |W ω i j| ^ (4 * p)) := fun ω =>
      cmp_rem_det hN hA (hW.symm ω) hz hηN hv i j ht htN p l hl
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
      (((cmp_measurable_rem A z v i j p l).comp hWm).norm.pow_const 2).aestronglyMeasurable
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
        _ = cmpKM p C * (N : ℝ) ^ (10 * p) := by
            unfold cmpKM; rw [mul_pow]; ring
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
private def cmpK1 (τ : ℝ) (p : ℕ) : ℝ :=
  ((4 * p + 1).factorial : ℝ) * (((4 * p + 1 : ℕ) : ℝ) + 1) ^ p *
    (37 * (1 + τ⁻¹)) ^ (4 * p + 1 + p) / τ ^ p

private lemma cmpK1_nonneg {τ : ℝ} (hτ : 0 < τ) (p : ℕ) : 0 ≤ cmpK1 τ p := by
  unfold cmpK1; positivity

/-- The union bound: nine events of probability `≤ N^{−(D−1)}` and one of probability `≤ N^{−D}`
have total probability `≤ N^{−(D−5)}`, for `N ≥ 2`. -/
private lemma cmp_prob_bound {Ω : Type} [MeasureSpace Ω] {N : ℕ} (hN : 2 ≤ N) {D : ℝ}
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
private lemma cmp_event {N : ℕ} (hN : 2 ≤ N) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 120) {p : ℕ} (hp2 : 2 ≤ p) (h36 : 36 * (1 + τ⁻¹) ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    (hK1 : cmpK1 τ p ≤ (N : ℝ) ^ (1 / 10 : ℝ)) {A : Matrix (Fin N) (Fin N) ℝ}
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
      {ω | ‖cmpRem A (W ω) z v i j p l‖ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p)} := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set u := cmpU v i j with hu
  have hun : ∀ a, testNorm (u a) = 1 := cmpU_testNorm hv i j
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
      ‖cmpRem A (W ω) z v i j p l‖ ≤ τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p) := by
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
        rw [cmp_ent_sub]; ring
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
    have hR := cmp_rem_good hA (hWs ω) hz v i j hG hPv h36' p l hl
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
      unfold cmpK1 at h
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
  have hsub : {ω | ‖cmpRem A (W ω) z v i j p l‖ ≤
      τ ^ p * (N : ℝ) ^ ((l : ℝ) / 2 - 2 - p)}ᶜ ⊆ (⋃ a, ⋃ c, E a c) ∪ Ξᶜ := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists,
      not_not] at hc
    exact hω (hgood ω hc.1 hc.2)
  exact cmp_prob_bound hN E Ξ _ (fun a c => hr1 (u a) (u c)) hξ hsub


/-! ## Moment functions, product spaces and the laws of single entries -/

/-- `momMaxW` is idempotent. -/
private lemma cmp_momMaxW_idem (C : ℕ → ℝ) : momMaxW (momMaxW C) = momMaxW C := by
  funext p
  unfold momMaxW
  rw [max_assoc, max_self]

/-- The Gaussian moment term is bounded by `momMaxW`. -/
private lemma cmp_goe_le_momMaxW (C : ℕ → ℝ) (p : ℕ) :
    (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p ≤ momMaxW C p := le_max_right _ _

private lemma cmp_momMaxW_nonneg (C : ℕ → ℝ) (p : ℕ) : 0 ≤ momMaxW C p := by
  refine le_trans ?_ (cmp_goe_le_momMaxW C p)
  have : 0 ≤ gaussMoment p := by
    unfold gaussMoment; exact integral_nonneg fun x => by positivity
  positivity

/-- The interpolants lie in the class with moments `momMaxW C` when `W` does. -/
private lemma cmp_class_interp {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries (momMaxW C) N W) {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    WigClassEntries (momMaxW C)
      (Ω := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) N ofUpper := by
  have h := wigClass_interp hN hW h₀ h₁
  rwa [cmp_momMaxW_idem] at h

/-- The product space `∏_α ν_α` over the upper-triangular indices. -/
private def CmpPi (N : ℕ) (_ν : UpperIdx N → Measure ℝ) : Type := UpperIdx N → ℝ

private instance (N : ℕ) (ν : UpperIdx N → Measure ℝ) : MeasurableSpace (CmpPi N ν) :=
  MeasurableSpace.pi

private instance (N : ℕ) (ν : UpperIdx N → Measure ℝ) : MeasureSpace (CmpPi N ν) :=
  ⟨Measure.pi ν⟩

private lemma cmp_isProb_pi {N : ℕ} (ν : UpperIdx N → Measure ℝ) [∀ α, IsProbabilityMeasure (ν α)] :
    IsProbabilityMeasure (ℙ : Measure (CmpPi N ν)) := by
  change IsProbabilityMeasure (Measure.pi ν)
  infer_instance

/-- The moment, mean and variance conditions of the class for one law on `ℝ`. -/
private structure CmpULaw (N : ℕ) (C : ℕ → ℝ) (lo hi : ℝ) (ν : Measure ℝ) : Prop where
  integrable : ∀ p : ℕ, Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν
  mean : ∫ x, x ∂ν = 0
  var_ge : lo ≤ ∫ x, x ^ 2 ∂ν
  var_le : ∫ x, x ^ 2 ∂ν ≤ hi
  moment : ∀ p : ℕ, ∫ x, |Real.sqrt N * x| ^ p ∂ν ≤ C p

/-- The upper index `(min i j, max i j)` of the entry `(i, j)`. -/
private def cmpUp {N : ℕ} (i j : Fin N) : UpperIdx N := ⟨(min i j, max i j), min_le_max⟩

/-- The variance bound of the entry `α`: `2/N` on the diagonal and `1/N` off it. -/
private def cmpVarHi (N : ℕ) (α : UpperIdx N) : ℝ := if α.1.1 = α.1.2 then 2 / (N : ℝ) else 1 / N

private lemma cmp_goeLaw_prob (N : ℕ) (α : UpperIdx N) : IsProbabilityMeasure (goeLaw N α) := by
  unfold goeLaw
  infer_instance

private lemma cmp_entryLawW_prob {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (α : UpperIdx N) : IsProbabilityMeasure (entryLawW W α) :=
  ⟨by simp [entryLawW, Measure.map_apply (hW α.1.1 α.1.2) MeasurableSet.univ]⟩

/-- The entry law `α` of a matrix in the class satisfies `CmpULaw`. -/
private lemma cmp_entryLawW_uLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N) :
    CmpULaw N C (1 / N) (cmpVarHi N α) (entryLawW W α) := by
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
    · simp only [cmpVarHi, h, ite_true]
      exact hW.var_diag_le _
    · simp only [cmpVarHi, h, ite_false]
      exact (hW.var_off _ _ h).le
  · exact (key (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le (hW.moment p _ _)

private lemma CmpULaw.mono {N : ℕ} {C C' : ℕ → ℝ} {lo hi : ℝ} {ν : Measure ℝ}
    (h : CmpULaw N C lo hi ν)
    (hC : ∀ p, C p ≤ C' p) : CmpULaw N C' lo hi ν :=
  ⟨h.integrable, h.mean, h.var_ge, h.var_le, fun p => (h.moment p).trans (hC p)⟩

/-- The entry law of the GOE matrix `goeW N` is `goeLaw N`. -/
private lemma cmp_entryLawW_goeW (N : ℕ) (α : UpperIdx N) : entryLawW (goeW N) α = goeLaw N α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  change i ≤ j at hij
  simp only [entryLawW, goeLaw]
  rcases hij.lt_or_eq with h | h
  · rw [(isGOE_goeW N).law_off i j h]
    simp [goeVar, h.ne]
  · subst h
    rw [(isGOE_goeW N).law_diag i]
    simp [goeVar]

/-- The GOE entry law satisfies `CmpULaw` with moments `momMaxW C`. -/
private lemma cmp_goeLaw_uLaw {N : ℕ} (hN : 1 ≤ N) (C : ℕ → ℝ) (α : UpperIdx N) :
    CmpULaw N (momMaxW C) (1 / N) (cmpVarHi N α) (goeLaw N α) := by
  rw [← cmp_entryLawW_goeW]
  exact (cmp_entryLawW_uLaw ((isGOE_goeW N).classEntries hN) α).mono
    (cmp_goe_le_momMaxW C)

/-- Integrability of `|√N x|^p` gives integrability of `x^p`. -/
private lemma cmp_integrable_pow_of_sqrt {N : ℕ} (hN : 1 ≤ N) {ν : Measure ℝ} {p : ℕ}
    (h : Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν) :
    Integrable (fun x : ℝ => x ^ p) ν := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine (h.const_mul ((Real.sqrt N)⁻¹ ^ p)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hs.ne', one_pow, one_mul]

private lemma cmp_integrable_mix {θ : ℝ} {ρ₀ ρ₁ : Measure ℝ} {f : ℝ → ℝ}
    (hf₀ : Integrable f ρ₀) (hf₁ : Integrable f ρ₁) : Integrable f (mixMeasure θ ρ₀ ρ₁) :=
  (hf₁.smul_measure ENNReal.ofReal_ne_top).add_measure (hf₀.smul_measure ENNReal.ofReal_ne_top)

/-- A mixture of two laws satisfying `CmpULaw` with the same moment function satisfies it. -/
private lemma CmpULaw.mix {N : ℕ} (hN : 1 ≤ N) {C : ℕ → ℝ} {lo hi : ℝ} {ν₀ ν₁ : Measure ℝ}
    (h₀ : CmpULaw N C lo hi ν₀) (h₁ : CmpULaw N C lo hi ν₁) {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) : CmpULaw N C lo hi (mixMeasure θ ν₀ ν₁) := by
  have hi : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ p) ν₀ ∧ Integrable (fun x : ℝ => x ^ p) ν₁ :=
    fun p => ⟨cmp_integrable_pow_of_sqrt hN (h₀.integrable p),
      cmp_integrable_pow_of_sqrt hN (h₁.integrable p)⟩
  have hvar := integral_mixMeasure hθ₀ hθ₁ (hi 2).1 (hi 2).2
  have hc : 0 ≤ 1 - θ := sub_nonneg.2 hθ₁
  refine ⟨fun p => cmp_integrable_mix (h₀.integrable p) (h₁.integrable p), ?_, ?_, ?_,
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
private lemma cmp_integral_coord {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)]
    (α : UpperIdx N) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (ν α)) :
    ∫ ω : CmpPi N ν, f (ω α) = ∫ x, f x ∂(ν α) :=
  integral_comp_eval (μ := ν) hf

private lemma cmp_integrable_coord {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)] (α : UpperIdx N) {f : ℝ → ℝ} (hf : Integrable f (ν α)) :
    Integrable (fun ω : CmpPi N ν => f (ω α)) := integrable_comp_eval (μ := ν) hf

/-- The coordinate matrix under a product of laws satisfying `CmpULaw` lies in the class. -/
private lemma cmp_class_pi {C : ℕ → ℝ} {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)] (hν : ∀ α, CmpULaw N C (1 / N) (cmpVarHi N α) (ν α)) :
    WigClassEntries C (Ω := CmpPi N ν) N ofUpper := by
  have key : ∀ (i j : Fin N) (f : ℝ → ℝ), Continuous f →
      ∫ ω : CmpPi N ν, f (ofUpper ω i j) = ∫ x, f x ∂(ν (cmpUp i j)) :=
    fun i j f hf => cmp_integral_coord ν (cmpUp i j) hf.aestronglyMeasurable
  refine ⟨fun i j => measurable_pi_apply (X := fun _ : UpperIdx N => ℝ) (cmpUp i j),
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
  · exact (key i j (fun x => x) continuous_id).trans (hν (cmpUp i j)).mean
  · have hv := hν (cmpUp i j)
    have hne : (cmpUp i j).1.1 ≠ (cmpUp i j).1.2 := fun h =>
      hij (le_antisymm ((le_max_left i j).trans (h.symm.le.trans (min_le_right i j)))
        ((le_max_right i j).trans (h.symm.le.trans (min_le_left i j))))
    have e := key i j (fun x => x ^ 2) (by fun_prop)
    have hle : ∫ x, x ^ 2 ∂(ν (cmpUp i j)) ≤ 1 / (N : ℝ) := by
      have := hv.var_le
      simpa only [cmpVarHi, hne, ite_false] using this
    exact e.trans (le_antisymm hle hv.var_ge)
  · have e := key i i (fun x => x ^ 2) (by fun_prop)
    exact (hν (cmpUp i i)).var_ge.trans_eq e.symm
  · have e := key i i (fun x => x ^ 2) (by fun_prop)
    have hv : cmpVarHi N (cmpUp i i) = 2 / (N : ℝ) := by simp [cmpVarHi, cmpUp]
    exact e.trans_le (hv ▸ (hν (cmpUp i i)).var_le)
  · exact cmp_integrable_coord ν (cmpUp i j)
      (f := fun x : ℝ => |Real.sqrt N * x| ^ p) ((hν (cmpUp i j)).integrable p)
  · exact (key i j (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le
      ((hν (cmpUp i j)).moment p)

/-- The coordinate matrix has vanishing third moments when every coordinate law has. -/
private lemma cmp_zeroThird_pi {N : ℕ} (ν : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ν α)]
    (h3 : ∀ α, ∫ x, x ^ 3 ∂(ν α) = 0) :
    ∀ i j, ∫ ω : CmpPi N ν, (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) i j ^ 3 = 0 := by
  intro i j
  have e := cmp_integral_coord ν (cmpUp i j) (f := fun x : ℝ => x ^ 3)
    (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable
  exact e.trans (h3 _)

/-- The third moment of a centred Gaussian vanishes. -/
private lemma cmp_integral_cube_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  have h := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ => -x) (f := fun x : ℝ => x ^ 3)
    (by fun_prop) (by fun_prop)
  rw [gaussianReal_map_neg, neg_zero] at h
  have e : ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) := fun x => by ring
  simp_rw [e, integral_neg] at h
  linarith

/-- The pair family: the interpolating laws, with the factor `α` replaced by `ρ`. -/
private def cmpPairLaw {N : ℕ} (θ : ℝ) (ρ₀ ρ₁ : UpperIdx N → Measure ℝ) (α : UpperIdx N)
    (ρ : Measure ℝ) : UpperIdx N → Measure ℝ :=
  Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ

private lemma cmp_pairLaw_prob {N : ℕ} (θ : ℝ) (ρ₀ ρ₁ : UpperIdx N → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (β : UpperIdx N) :
    IsProbabilityMeasure (cmpPairLaw θ ρ₀ ρ₁ α ρ β) := by
  unfold cmpPairLaw
  by_cases h : β = α
  · subst h; simpa using ‹IsProbabilityMeasure ρ›
  · simpa [Function.update_of_ne h] using isProbabilityMeasure_mixMeasure θ (ρ₀ β) (ρ₁ β)

/-- The pair matrices lie in the class with moments `momMaxW C`. -/
private lemma cmp_class_pair {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries (momMaxW C) N W) {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : CmpULaw N (momMaxW C) (1 / N) (cmpVarHi N α) ρ) :
    haveI : ∀ α, IsProbabilityMeasure (goeLaw N α) := cmp_goeLaw_prob N
    haveI : ∀ α, IsProbabilityMeasure (entryLawW W α) := cmp_entryLawW_prob hW.measurable
    haveI := cmp_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
    WigClassEntries (momMaxW C)
      (Ω := CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α ρ)) N ofUpper := by
  have : ∀ α, IsProbabilityMeasure (goeLaw N α) := cmp_goeLaw_prob N
  have : ∀ α, IsProbabilityMeasure (entryLawW W α) := cmp_entryLawW_prob hW.measurable
  have := cmp_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
  refine cmp_class_pi _ fun β => ?_
  unfold cmpPairLaw
  by_cases h : β = α
  · subst h
    simpa using hρ
  · rw [Function.update_of_ne h]
    exact (cmp_goeLaw_uLaw hN C β).mix hN (cmp_entryLawW_uLaw hW β) h₀ h₁

/-- Third moment of the entry law of a matrix with vanishing third moments. -/
private lemma cmp_entryLawW_third {Ω : Type*} [MeasureSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (h3 : ∀ i j, ∫ ω, W ω i j ^ 3 = 0) (α : UpperIdx N) : ∫ x, x ^ 3 ∂(entryLawW W α) = 0 :=
  (integral_map (hW α.1.1 α.1.2).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable).trans (h3 _ _)

/-- The pair matrices have vanishing third moments when `W` has. -/
private lemma cmp_zeroThird_pair {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (h3 : ∀ i j, ∫ ω, W ω i j ^ 3 = 0) {θ : ℝ} (h₀ : 0 ≤ θ)
    (h₁ : θ ≤ 1) (α : UpperIdx N) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∫ x, x ^ 3 ∂ρ = 0) :
    haveI : ∀ α, IsProbabilityMeasure (goeLaw N α) := cmp_goeLaw_prob N
    haveI : ∀ α, IsProbabilityMeasure (entryLawW W α) := cmp_entryLawW_prob hW.measurable
    haveI := cmp_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
    ∀ i j, ∫ ω : CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α ρ),
      (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) i j ^ 3 = 0 := by
  have : ∀ α, IsProbabilityMeasure (goeLaw N α) := cmp_goeLaw_prob N
  have : ∀ α, IsProbabilityMeasure (entryLawW W α) := cmp_entryLawW_prob hW.measurable
  have := cmp_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
  refine cmp_zeroThird_pi _ fun β => ?_
  unfold cmpPairLaw
  by_cases h : β = α
  · subst h
    simpa using hρ
  · rw [Function.update_of_ne h]
    have hi₀ := cmp_integrable_pow_of_sqrt hN ((cmp_goeLaw_uLaw hN C β).integrable 3)
    have hi₁ := cmp_integrable_pow_of_sqrt hN ((cmp_entryLawW_uLaw hW β).integrable 3)
    rw [integral_mixMeasure h₀ h₁ hi₀ hi₁, cmp_entryLawW_third hW.measurable h3 β]
    have : ∫ x, x ^ 3 ∂(goeLaw N β) = 0 := cmp_integral_cube_gaussianReal _
    rw [this]
    ring

/-- The interpolants have vanishing third moments when `W` has. -/
private lemma cmp_zeroThird_interp {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (h3 : ∀ i j, ∫ ω, W ω i j ^ 3 = 0) {θ : ℝ} (h₀ : 0 ≤ θ)
    (h₁ : θ ≤ 1) :
    zeroThirdW (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper :=
  zeroThirdW_interp hN hW h3 h₀ h₁

/-! ## Integrals of invariant functions and endpoint laws -/

/-- A bounded measurable real function not depending on the coordinate `α` has the same
integral under `interpLawAt θ ρ₀ ρ₁ α ρ` and under `interpLaw θ ρ₀ ρ₁`. -/
private lemma cmp_integral_inv_real {N : ℕ} {θ : ℝ} {ρ₀ ρ₁ : UpperIdx N → Measure ℝ}
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {h : (UpperIdx N → ℝ) → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, |h x| ≤ B) (hinv : ∀ x t, h (Function.update x α t) = h x) :
    ∫ x, h x ∂(interpLawAt θ ρ₀ ρ₁ α ρ) = ∫ x, h x ∂(interpLaw θ ρ₀ ρ₁) := by
  have := cmp_pairLaw_prob θ ρ₀ ρ₁ α ρ
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have : IsProbabilityMeasure (interpLaw θ ρ₀ ρ₁) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure (interpLawAt θ ρ₀ ρ₁ α ρ) := by
    unfold interpLawAt
    change IsProbabilityMeasure (Measure.pi (cmpPairLaw θ ρ₀ ρ₁ α ρ))
    infer_instance
  have hint : Integrable h (interpLawAt θ ρ₀ ρ₁ α ρ) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  rw [integral_interpLawAt_eq α ρ hm hint]
  simp_rw [hinv]
  rw [integral_fun_fst]
  simp

/-- The complex version of `cmp_integral_inv_real`. -/
private lemma cmp_integral_inv {N : ℕ} {θ : ℝ} {ρ₀ ρ₁ : UpperIdx N → Measure ℝ}
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : UpperIdx N)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {h : (UpperIdx N → ℝ) → ℂ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (hinv : ∀ x t, h (Function.update x α t) = h x) :
    ∫ x, h x ∂(interpLawAt θ ρ₀ ρ₁ α ρ) = ∫ x, h x ∂(interpLaw θ ρ₀ ρ₁) := by
  have := cmp_pairLaw_prob θ ρ₀ ρ₁ α ρ
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have : IsProbabilityMeasure (interpLawAt θ ρ₀ ρ₁ α ρ) := by
    unfold interpLawAt
    change IsProbabilityMeasure (Measure.pi (cmpPairLaw θ ρ₀ ρ₁ α ρ))
    infer_instance
  have : IsProbabilityMeasure (interpLaw θ ρ₀ ρ₁) := by
    unfold interpLaw
    infer_instance
  have hi1 : Integrable h (interpLawAt θ ρ₀ ρ₁ α ρ) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hi2 : Integrable h (interpLaw θ ρ₀ ρ₁) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hre := cmp_integral_inv_real (θ := θ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) α ρ
    (h := fun x => (h x).re) (Complex.measurable_re.comp hm) (B := B)
    (fun x => (Complex.abs_re_le_norm _).trans (hB x)) (fun x t => by simp only [hinv])
  have him := cmp_integral_inv_real (θ := θ) (ρ₀ := ρ₀) (ρ₁ := ρ₁) α ρ
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

private lemma cmp_interpLaw_one {N : ℕ} (ρ₀ ρ₁ : UpperIdx N → Measure ℝ) :
    interpLaw 1 ρ₀ ρ₁ = Measure.pi ρ₁ := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

private lemma cmp_interpLaw_zero {N : ℕ} (ρ₀ ρ₁ : UpperIdx N → Measure ℝ) :
    interpLaw 0 ρ₀ ρ₁ = Measure.pi ρ₀ := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

/-- The upper-triangular coordinates of a symmetric matrix determine it. -/
private lemma cmp_ofUpper_restrict {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : Mᵀ = M) :
    ofUpper (fun β : UpperIdx N => M β.1.1 β.1.2) = M := by
  ext i j
  simp only [ofUpper]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact congrFun (congrFun hM i) j

/-- For a matrix of the class, the law of its upper coordinates is the product of the entry
laws. -/
private lemma cmp_integral_pi_entryLaw {Ω : Type*} [MeasureSpace Ω]
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
  rw [cmp_ofUpper_restrict (hW.symm ω)]

private lemma cmp_measurable_ofUpper {N : ℕ} :
    Measurable (ofUpper : (UpperIdx N → ℝ) → Matrix (Fin N) (Fin N) ℝ) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    measurable_pi_apply (X := fun _ : UpperIdx N => ℝ) (cmpUp i j)

private lemma cmp_measurable_Fv {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ) :
    Measurable fun M : Matrix (Fin N) (Fin N) ℝ => FvW A M z v := by
  unfold FvW
  have h1 : Measurable fun M : Matrix (Fin N) (Fin N) ℝ => GW A M z - piW A z :=
    (cmp_measurable_G A z).sub measurable_const
  exact ((cmp_continuous_ent v v).measurable.comp h1).norm

private lemma cmp_ofUpper_symm {N : ℕ} (x : UpperIdx N → ℝ) :
    (ofUpper x : Matrix (Fin N) (Fin N) ℝ)ᵀ = ofUpper x := by
  ext i j
  simp [ofUpper, min_comm, max_comm]

/-- `F_v ≤ η⁻¹ + τ⁻¹` for a symmetric `W`, `|v| = 1`, `z` in a set with the standing bound. -/
private lemma cmp_Fv_le {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {A Wm : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hW : Wmᵀ = Wm) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hz : z ∈ S) (hzim : 0 < z.im) {v : Fin N → ℝ} (hv : testNorm v = 1) :
    FvW A Wm z v ≤ z.im⁻¹ + τ⁻¹ := by
  unfold FvW
  rw [cmp_ent_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have h := cmp_ent_le hA hW hzim v v
    rwa [hv, mul_one, mul_one] at h
  · have h := norm_piW_le hτ hA hS hz v v
    rwa [hv, mul_one, mul_one] at h


/-! ## The expansion of one Lindeberg term -/

private lemma cmp_up_self {N : ℕ} (α : UpperIdx N) : cmpUp α.1.1 α.1.2 = α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  simp only [cmpUp]
  congr
  · exact min_eq_left hij
  · exact max_eq_right hij

/-- Updating the coordinate `α` does not change `W^{(α),0}`. -/
private lemma cmp_Wupd_ofUpper_update {N : ℕ} (x : UpperIdx N → ℝ) (α : UpperIdx N) (t s : ℝ) :
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

private lemma cmp_resCoeffW_zero {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v : Fin N → ℝ)
    (i j : Fin N) : resCoeffW A Wm z v i j 0 = ent (GW A Wm z - piW A z) v v := by
  simp [resCoeffW]

private lemma cmp_fCoeff_zero_eq {N : ℕ} {p : ℕ} (hp : Even p) (A Wm : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (v : Fin N → ℝ) (i j : Fin N) :
    fCoeff p (resCoeffW A Wm z v i j) 0 = ((FvW A Wm z v ^ p : ℝ) : ℂ) := by
  rw [fCoeff_zero hp, cmp_resCoeffW_zero]
  unfold FvW
  push_cast
  rfl

/-- `z.im⁻¹ ≤ N` on `𝐃^W(τ, N)`. -/
private lemma cmp_im_inv_le {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {z : ℂ} (hz : z ∈ domW τ N) :
    z.im⁻¹ ≤ N := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  obtain ⟨hη0, -, hηl, -⟩ := hz
  have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ z.im :=
    (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)).trans hηl
  rw [Real.rpow_neg_one] at h1
  exact (inv_le_comm₀ hη0 hNp).2 h1

/-- One Lindeberg term: for the pair matrix with the entry `α` drawn from `ρ`,
`E F_v^p = ∑_{k ≤ 4p} E y^k · E f_k(W^{θ,(α),0}) + R` with `|R| ≤ 2 τ^p N^{−2−p}`. -/
private lemma cmp_pair_expand (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (Q : ModelClassW N)
      (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N (momMaxW C) Q A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W →
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ (α : UpperIdx N) (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
        CmpULaw N (momMaxW C) (1 / N) (cmpVarHi N α) ρ →
        Q (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α ρ)) ofUpper →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
        ∃ R : ℂ, ‖R‖ ≤ 2 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) ∧
          ((∫ x, FvW A (ofUpper x) z v ^ p ∂(interpLawAt θ (goeLaw N) (entryLawW W) α ρ) : ℝ)
            : ℂ) =
            ∑ k ∈ Finset.range (4 * p + 1), (∫ y, (y : ℂ) ^ k ∂ρ) *
              (∫ x, fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k
                ∂(interpLaw θ (goeLaw N) (entryLawW W))) + R := by
  have hδ1 : δ ≤ 1 / 120 := by nlinarith
  obtain ⟨N₁, h₁⟩ := wig_rough_bound τ (momMaxW C) C₀ δ (δ / 4) (dPrev p) hτ hτ1 hδ hC₀ hC₀δ
    (by positivity)
  obtain ⟨N₂, h₂⟩ := cmp_markov (momMaxW C) (δ / 4) (dPrev p) (by positivity)
  set K36 : ℝ := 36 * (1 + τ⁻¹) with hK36
  have hK360 : 0 ≤ K36 := by positivity
  refine ⟨max (max (max N₁ N₂) (max 2 ⌈τ⁻¹⌉₊))
    (max (max ⌈K36 ^ (1 / 4 : ℝ)⁻¹⌉₊ ⌈cmpK1 τ p ^ (1 / 10 : ℝ)⁻¹⌉₊) ⌈cmpKM p (momMaxW C)⌉₊), ?_⟩
  intro N hN A S Q m hset hm hPA Ω _ _ W hW θ hθ α ρ _ hρ hQ z hz v hv
  have hNN₁ : N₁ ≤ N := by omega
  have hNN₂ : N₂ ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have h36N : ⌈K36 ^ (1 / 4 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hK1N : ⌈cmpK1 τ p ^ (1 / 10 : ℝ)⁻¹⌉₊ ≤ N := by omega
  have hKMN : ⌈cmpKM p (momMaxW C)⌉₊ ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have h36 : K36 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := cmp_le_rpow hK360 (by norm_num) h36N
  have hK1 : cmpK1 τ p ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    cmp_le_rpow (cmpK1_nonneg hτ p) (by norm_num) hK1N
  have hKM : cmpKM p (momMaxW C) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hKMN)
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have hη0 : 0 < z.im := hzD.1
  have hηN : z.im⁻¹ ≤ N := cmp_im_inv_le hN1 hτ hzD
  have hPi : ∀ x y : Fin N → ℝ, ‖ent (piW A z) x y‖ ≤ τ⁻¹ * testNorm x * testNorm y :=
    fun x y => norm_piW_le hτ hset.symmA hset.standing hzS x y
  have hPv : ‖ent (piW A z) v v‖ ≤ τ⁻¹ := by
    have := hPi v v
    rwa [hv, mul_one, mul_one] at this
  -- the pair space
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := cmp_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := cmp_entryLawW_prob hW.measurable
  set ν := cmpPairLaw θ (goeLaw N) (entryLawW W) α ρ with hν
  have : ∀ β, IsProbabilityMeasure (ν β) := cmp_pairLaw_prob θ (goeLaw N) (entryLawW W) α ρ
  have : IsProbabilityMeasure (ℙ : Measure (CmpPi N ν)) := cmp_isProb_pi ν
  have hY : WigClassEntries (momMaxW C) (Ω := CmpPi N ν) N ofUpper :=
    cmp_class_pair hN1 hW hθ.1 hθ.2 α ρ hρ
  have hr1 := (h₁ N hNN₁ A S Q m hset hm hPA (CmpPi N ν) ofUpper hY hQ z hz).1
  have hξ := h₂ N hNN₂ (Ω := CmpPi N ν)
    (fun ω => (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2)
    (fun q => ⟨hY.integrable_moment q _ _, hY.moment q _ _⟩)
  have hev := cmp_event hN2 hτ hδ hδ1 hp2 h36 hK1 hset.symmA hη0 hv hPi hY.symm hr1
    α.1.1 α.1.2 hξ 0 (Nat.zero_le _)
  have hD : 3 * ((10 * p + 1 : ℕ) : ℝ) ≤ dPrev p - 5 := by
    unfold dPrev
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    push_cast
    nlinarith
  have hτge : (N : ℝ)⁻¹ ≤ τ := by
    rw [inv_le_comm₀ hNp hτ]; exact hτN
  have hΓ : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤
      τ ^ p * (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2 - p) := by
    have h1 : ((N : ℝ)⁻¹) ^ p ≤ τ ^ p := pow_le_pow_left₀ (by positivity) hτge p
    have h3 : (N : ℝ) ^ (-((10 * p + 1 : ℕ) : ℝ)) ≤
        ((N : ℝ)⁻¹) ^ p * (N : ℝ) ^ (((0 : ℕ) : ℝ) / 2 - 2 - p) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le,
        ← Real.rpow_add hNp]
      refine Real.rpow_le_rpow_of_exponent_le hN1r ?_
      have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      push_cast
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hNp.le _))
  obtain ⟨hexp, hR⟩ := cmp_expect hN1 hset.symmA hη0 hηN hv hPv hτN hY α p 0 (Nat.zero_le _)
    (le_refl (0 : ℝ)) hD hΓ hKM hev
  refine ⟨∫ ω : CmpPi N ν, cmpRem A (ofUpper ω) z v α.1.1 α.1.2 p 0, ?_, ?_⟩
  · refine hR.trans (le_of_eq ?_)
    simp
  · -- the left side
    have hL : ((∫ x, FvW A (ofUpper x) z v ^ p ∂(interpLawAt θ (goeLaw N) (entryLawW W) α ρ) : ℝ)
        : ℂ) = ∫ ω : CmpPi N ν, fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) 0 := by
      simp_rw [cmp_fCoeff_zero_eq hp]
      rw [integral_complex_ofReal]
      rfl
    rw [hL, hexp]
    congr 1
    simp only [Nat.sub_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 4 * p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hmom : ∫ ω : CmpPi N ν, ((ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2 : ℂ) ^ k =
        ∫ y, (y : ℂ) ^ k ∂ρ := by
      have h := cmp_integral_coord ν α (f := fun y : ℝ => (y : ℂ) ^ k) (by fun_prop)
      have hνα : ν α = ρ := by simp [hν, cmpPairLaw]
      rw [hνα] at h
      refine Eq.trans ?_ h
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have e : (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) α.1.1 α.1.2 =
          (show UpperIdx N → ℝ from ω) α := by
        change (show UpperIdx N → ℝ from ω) (cmpUp α.1.1 α.1.2) = _
        rw [cmp_up_self]
      simp only [e]
    have hm : Measurable fun x : UpperIdx N → ℝ =>
        fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k :=
      (cmp_measurable_fUpd A z v α.1.1 α.1.2 p k 0).comp cmp_measurable_ofUpper
    have hB : ∀ x : UpperIdx N → ℝ,
        ‖fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k‖ ≤
          ((4 * p + 1 : ℕ) : ℝ) ^ p * (4 * N) ^ (5 * p) := fun x =>
      cmp_f_det hN1 hset.symmA (cmp_Wupd_symm (cmp_ofUpper_symm x) _ _ 0) hη0 hηN hv
        α.1.1 α.1.2 hPv hτN p k hk'
    have hinv : ∀ (x : UpperIdx N → ℝ) (t : ℝ),
        fCoeff p (resCoeffW A (Wupd (ofUpper (Function.update x α t)) α.1.1 α.1.2 0) z v
          α.1.1 α.1.2) k =
        fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k := by
      intro x t
      rw [cmp_Wupd_ofUpper_update]
    have hcoef : ∫ ω : CmpPi N ν,
        fCoeff p (resCoeffW A (Wupd (ofUpper ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k =
        ∫ x, fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k
          ∂(interpLaw θ (goeLaw N) (entryLawW W)) :=
      cmp_integral_inv (θ := θ) (ρ₀ := goeLaw N) (ρ₁ := entryLawW W) α ρ hm hB hinv
    rw [hmom, hcoef]


/-! ## The derivative of `θ ↦ E F_v^p(W^θ)` -/

/-- The moments of a law satisfying `CmpULaw`. -/
private lemma cmp_law_mom {N : ℕ} (hN : 1 ≤ N) {C : ℕ → ℝ} {lo hi : ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (h : CmpULaw N C lo hi ν) :
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
private lemma cmp_psi_ge {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (a : Fin N → ℝ) {z : ℂ}
    (hz : z ∈ domW τ N) : τ / N ≤ PsiW a z := by
  obtain ⟨h0, -, -, hη⟩ := hz
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have h1 : τ / N ≤ 1 / (N * z.im) := by
    rw [div_le_div_iff₀ hNp (by positivity), one_mul]
    calc τ * (N * z.im) ≤ τ * (N * τ⁻¹) := by gcongr
      _ = N := by field_simp
  unfold PsiW
  linarith [Real.sqrt_nonneg ((mW a z).im / (N * z.im))]

private lemma cmp_card_upper (N : ℕ) : (Fintype.card (UpperIdx N) : ℝ) ≤ (N : ℝ) ^ 2 := by
  have h := Fintype.card_subtype_le (fun q : Fin N × Fin N => q.1 ≤ q.2)
  rw [Fintype.card_prod, Fintype.card_fin] at h
  have : (Fintype.card (UpperIdx N) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h
  rw [sq]; push_cast at this; exact this

/-- The sum over the diagonal upper indices is the sum over `Fin N`. -/
private lemma cmp_sum_diag {N : ℕ} (g : Fin N → ℝ) :
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

/-- The Lindeberg derivative bound: `|d/dθ E F_v^p(W^θ)| ≤ K (b + X + E F_v^p(W^θ))` with
`b = (N^{C₀δ} Ψ)^p`, where `X` controls the third-order term. -/
private lemma cmp_deriv_bound (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ K3 : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4)
    (hK3 : 0 ≤ K3) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (Q : ModelClassW N) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N (momMaxW C) Q A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1,
        Q (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ α : UpperIdx N,
        Q (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α (entryLawW W α))) ofUpper ∧
        Q (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α (goeLaw N α))) ofUpper) →
      ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 → ∀ X : ℝ, 0 ≤ X →
      ((∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0) ∨
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ s : UpperIdx N → ℂ, (∀ α, ‖s α‖ ≤ 1) →
          (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α *
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) 3‖ ≤
            K3 * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p + X +
              ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                FvW A (ofUpper ω) z v ^ p)) →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        |∑ α : UpperIdx N,
          ((∫ x, FvW A (ofUpper x) z v ^ p
              ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α))) -
            ∫ x, FvW A (ofUpper x) z v ^ p
              ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α)))| ≤
          K' * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p + X +
            ∫ x, FvW A (ofUpper x) z v ^ p ∂(interpLaw θ (goeLaw N) (entryLawW W))) := by
  obtain ⟨Kz, hKz, Nz, hZt⟩ := wig_zero_to_theta τ (momMaxW C) p C₀ δ hτ hτ1 hp hp2 hδ hC₀ hC₀δ
  obtain ⟨Kh, hKh, Nh, hh⟩ := wig_coeff_high τ (momMaxW C) p C₀ δ hτ hτ1 hp hp2 hδ hC₀ hC₀δ
  obtain ⟨Kd, hKd, Nd, hd⟩ := wig_coeff_diag τ (momMaxW C) p C₀ δ hτ hτ1 hp hp2 hδ hC₀ hC₀δ
  obtain ⟨Ne, he⟩ := cmp_pair_expand τ C p C₀ δ hτ hτ1 hp hp2 hδ hC₀ hC₀δ
  set c : ℕ → ℝ := fun k => 2 * momMaxW C k + 1 with hc
  have hc1 : ∀ k, 1 ≤ c k := fun k => by
    have := cmp_momMaxW_nonneg C k; simp only [hc]; linarith
  set Csum : ℝ := ∑ k ∈ Finset.range (4 * p + 1), c k with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun k _ => (zero_le_one.trans (hc1 k))
  set Kb : ℝ := Kd + K3 + Kh with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  refine ⟨Csum * Kz * (Kb + 1 + 4 * p * Kh) + 4, by positivity,
    max (max (max Nz Nh) (max Nd Ne)) (max 1 ⌈τ⁻¹⌉₊), ?_⟩
  intro N hN A S Q m hset hm hPA Ω _ _ W hW hQ1 hQ2 z hz v hv X hX h3 θ hθ
  have hNz : Nz ≤ N := by omega
  have hNh : Nh ≤ N := by omega
  have hNd : Nd ≤ N := by omega
  have hNe : Ne ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := cmp_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := cmp_entryLawW_prob hW.measurable
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (goeLaw N β) (entryLawW W β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (goeLaw N) (entryLawW W)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure
      (ℙ : Measure (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W))) := hIP
  have hWθ : WigClassEntries (momMaxW C)
      (Ω := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) N ofUpper :=
    cmp_class_interp hN1 hW hθ.1 hθ.2
  have hQθ := hQ1 θ hθ
  -- notation
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨ : τ / N ≤ Ψ := cmp_psi_ge hN1 hτ _ hzD
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨ
  set b : ℝ := ((N : ℝ) ^ (C₀ * δ) * Ψ) ^ p with hb
  have hb0 : 0 ≤ b := by positivity
  set Φθ : ℝ := ∫ x, FvW A (ofUpper x) z v ^ p ∂(interpLaw θ (goeLaw N) (entryLawW W))
    with hΦθ
  have hΦθ0 : 0 ≤ Φθ := integral_nonneg fun x => by unfold FvW; positivity
  have hNδb : (N : ℝ) ^ δ * Ψ ^ p ≤ b := by
    rw [hb, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hΨ0 p)
    calc (N : ℝ) ^ δ ≤ (N : ℝ) ^ (C₀ * δ) := Real.rpow_le_rpow_of_exponent_le hN1r (by nlinarith)
      _ ≤ ((N : ℝ) ^ (C₀ * δ)) ^ p :=
          le_self_pow₀ (Real.one_le_rpow hN1r (by nlinarith)) (by omega)
  have hΨb : Ψ ^ p ≤ b := by
    refine le_trans ?_ hNδb
    exact le_mul_of_one_le_left (pow_nonneg hΨ0 p) (Real.one_le_rpow hN1r hδ.le)
  -- the coefficient bounds at `W^θ`
  have hHigh := hh N hNh A S Q m hset hm hPA
    (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ hQθ z hz v hv
  have hDiag := hd N hNd A S Q m hset hm hPA
    (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ hQθ z hz v hv
  have hZ := hZt N hNz A S Q m hset hm hPA
    (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ hQθ z hz v hv
  -- the expansions of the Lindeberg terms
  have hexp : ∀ (α : UpperIdx N) (b : Bool), ∃ R : ℂ,
      ‖R‖ ≤ 2 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) ∧
      ((∫ x, FvW A (ofUpper x) z v ^ p ∂(interpLawAt θ (goeLaw N) (entryLawW W) α
          (if b then entryLawW W α else goeLaw N α)) : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (4 * p + 1),
          (∫ y, (y : ℂ) ^ k ∂(if b then entryLawW W α else goeLaw N α)) *
          (∫ x, fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k
            ∂(interpLaw θ (goeLaw N) (entryLawW W))) + R := by
    intro α b
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact he N hNe A S Q m hset hm hPA Ω W hW θ hθ α (goeLaw N α) (cmp_goeLaw_uLaw hN1 C α)
        (hQ2 θ hθ α).2 z hz v hv
    · simp only [↓reduceIte]
      exact he N hNe A S Q m hset hm hPA Ω W hW θ hθ α (entryLawW W α)
        (cmp_entryLawW_uLaw hW α) (hQ2 θ hθ α).1 z hz v hv
  choose R hRb hReq using hexp
  -- moments of the two entry laws
  set μ : Bool → UpperIdx N → ℕ → ℂ := fun b α k =>
    ∫ y, (y : ℂ) ^ k ∂(if b then entryLawW W α else goeLaw N α) with hμ
  have hlaw : ∀ (b : Bool) (α : UpperIdx N),
      CmpULaw N (momMaxW C) (1 / N) (cmpVarHi N α) (if b then entryLawW W α else goeLaw N α) := by
    intro b α
    cases b
    · exact cmp_goeLaw_uLaw hN1 C α
    · exact cmp_entryLawW_uLaw hW α
  have hprob : ∀ (b : Bool) (α : UpperIdx N),
      IsProbabilityMeasure (if b then entryLawW W α else goeLaw N α) := by
    intro b α; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance
  have hmom : ∀ b α, (μ b α 0 = 1) ∧ (μ b α 1 = 0) ∧
      (α.1.1 ≠ α.1.2 → μ b α 2 = 1 / N) ∧
      ∀ k, ‖μ b α k‖ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * momMaxW C k := by
    intro b α
    have := hprob b α
    obtain ⟨h0, h1, h2, h4⟩ := cmp_law_mom hN1 (hlaw b α)
    refine ⟨h0, h1, fun hne => ?_, h4⟩
    have e := h2 (by simp [cmpVarHi, hne])
    simp only [hμ]
    rw [e]
    push_cast
    ring
  -- the differences of moments, normalised
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
      have : ∫ y, y ^ 3 ∂(goeLaw N α) = 0 := cmp_integral_cube_gaussianReal _
      rw [this]
      simp
    simp only [hd, e1, e0, sub_self]
  -- the coefficients `Z_k(α)`
  set Z : UpperIdx N → ℕ → ℂ := fun α k =>
    ∫ x, fCoeff p (resCoeffW A (Wupd (ofUpper x) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k
      ∂(interpLaw θ (goeLaw N) (entryLawW W)) with hZdef
  -- the derivative as a double sum
  have hder : ((∑ α : UpperIdx N,
      ((∫ x, FvW A (ofUpper x) z v ^ p
          ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α))) -
        ∫ x, FvW A (ofUpper x) z v ^ p
          ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α))) : ℝ) : ℂ) =
      (∑ k ∈ Finset.Ico 2 (4 * p + 1), ∑ α : UpperIdx N, d α k * Z α k) +
        ∑ α : UpperIdx N, (R α true - R α false) := by
    push_cast
    have e : ∀ α : UpperIdx N,
        ((∫ x, FvW A (ofUpper x) z v ^ p
            ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α)) : ℝ) : ℂ) -
          ((∫ x, FvW A (ofUpper x) z v ^ p
            ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α)) : ℝ) : ℂ) =
        (∑ k ∈ Finset.range (4 * p + 1), d α k * Z α k) + (R α true - R α false) := by
      intro α
      have e1 := hReq α true
      have e0 := hReq α false
      simp only [↓reduceIte, Bool.false_eq_true] at e1 e0
      rw [e1, e0]
      simp only [hd, hμ, hZdef, ↓reduceIte, Bool.false_eq_true, sub_mul,
        Finset.sum_sub_distrib]
      ring
    rw [Finset.sum_congr rfl fun α _ => e α, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ 4 * p + 1)]
    have h01 : ∑ k ∈ Finset.range 2, ∑ α : UpperIdx N, d α k * Z α k = 0 := by
      simp [Finset.sum_range_succ, (hd01 _).1, (hd01 _).2]
    rw [h01, zero_add]
  -- the bound for each order `k ∈ [2, 4p]`
  have hord : ∀ k ∈ Finset.Ico 2 (4 * p + 1), ‖∑ α : UpperIdx N, d α k * Z α k‖ ≤
      c k * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) := by
    intro k hk
    obtain ⟨hk2, hk4⟩ := Finset.mem_Ico.1 hk
    have hk4' : k ≤ 4 * p := Nat.lt_succ_iff.1 hk4
    set w : ℝ := (N : ℝ) ^ ((k : ℝ) / 2) / c k with hw
    have hck : 0 < c k := zero_lt_one.trans_le (hc1 k)
    have hw0 : 0 ≤ w := by positivity
    set s : UpperIdx N → ℂ := fun α => (w : ℂ) * d α k with hs
    have hNk : (N : ℝ) ^ ((k : ℝ) / 2) * (N : ℝ) ^ (-(k : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hNp, show (k : ℝ) / 2 + -(k : ℝ) / 2 = 0 by ring, Real.rpow_zero]
    have hs1 : ∀ α, ‖s α‖ ≤ 1 := by
      intro α
      simp only [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      calc w * ‖d α k‖ ≤ w * (c k * (N : ℝ) ^ (-(k : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hdk α k) hw0
        _ = 1 := by
            have e : w * (c k * (N : ℝ) ^ (-(k : ℝ) / 2)) =
                (N : ℝ) ^ ((k : ℝ) / 2) * (N : ℝ) ^ (-(k : ℝ) / 2) * (c k / c k) := by
              rw [hw]; ring
            rw [e, hNk, div_self hck.ne', mul_one]
    have hds : ∀ α, d α k = ((c k * (N : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) * s α := by
      intro α
      simp only [hs, hw]
      rw [← mul_assoc, ← Complex.ofReal_mul]
      have : c k * (N : ℝ) ^ (-(k : ℝ) / 2) * ((N : ℝ) ^ ((k : ℝ) / 2) / c k) = 1 := by
        have e : c k * (N : ℝ) ^ (-(k : ℝ) / 2) * ((N : ℝ) ^ ((k : ℝ) / 2) / c k) =
            (N : ℝ) ^ ((k : ℝ) / 2) * (N : ℝ) ^ (-(k : ℝ) / 2) * (c k / c k) := by ring
        rw [e, hNk, div_self hck.ne', mul_one]
      rw [this]; simp
    -- the bound `B` at `W^θ`
    have hB : (N : ℝ) ^ (-(k : ℝ) / 2) * ‖∑ α : UpperIdx N, s α *
        ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
          fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ ≤ Kb * (b + X + Φθ) := by
      have hNk0 : 0 ≤ (N : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg hNp.le _
      have hgen : ‖∑ α : UpperIdx N, s α *
          ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
            fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ ≤
          ∑ α : UpperIdx N, ‖s α‖ *
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
      have hint0 : ∀ α : UpperIdx N, 0 ≤ ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N)
          (entryLawW W), ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ :=
        fun α => integral_nonneg fun _ => norm_nonneg _
      rcases Nat.lt_or_ge k 4 with hk4l | hk4g
      · interval_cases k
        · -- k = 2: the diagonal
          have hs2 : ∀ α : UpperIdx N, ‖s α‖ *
              ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) 2‖ ≤
              if α.1.1 = α.1.2 then ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.1) 2‖ else 0 := by
            intro α
            by_cases hα : α.1.1 = α.1.2
            · rw [ite_eq_left hα]
              rw [← hα]
              exact mul_le_of_le_one_left (hint0 α |>.trans_eq (by rw [hα])) (hs1 α)
            · rw [ite_eq_right hα]
              simp [hs, hd2 α hα]
          have hsum := (hgen.trans (Finset.sum_le_sum fun α _ => hs2 α))
          rw [cmp_sum_diag (fun i => ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
            ‖fCoeff p (resCoeffW A (ofUpper ω) z v i i) 2‖)] at hsum
          rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at hNk0 ⊢
          rw [show (N : ℝ) ^ (-(2 : ℝ) / 2) = (N : ℝ)⁻¹ by
            rw [show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]]
          calc (N : ℝ)⁻¹ * _ ≤ (N : ℝ)⁻¹ * ∑ i : Fin N,
                ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                  ‖fCoeff p (resCoeffW A (ofUpper ω) z v i i) 2‖ :=
                mul_le_mul_of_nonneg_left hsum (by positivity)
            _ ≤ Kd * (b + Φθ) := hDiag
            _ ≤ Kb * (b + X + Φθ) := by
                have : Kd ≤ Kb := by simp only [hKb]; linarith
                exact mul_le_mul this (by linarith) (by linarith) hKb0
        · -- k = 3: the third-order term
          rcases h3 with h3l | h3r
          · have hs0 : ∀ α, s α = 0 := fun α => by simp [hs, hd3 h3l α]
            simp only [hs0, zero_mul, Finset.sum_const_zero, norm_zero, mul_zero]
            exact mul_nonneg hKb0 (by linarith)
          · have := h3r θ hθ s hs1
            have hE : (∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                FvW A (ofUpper ω) z v ^ p) = Φθ := rfl
            rw [hE] at this
            rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
            refine this.trans ?_
            have : K3 ≤ Kb := by simp only [hKb]; linarith
            exact mul_le_mul_of_nonneg_right this (by linarith)
      · -- k ≥ 4
        have hs4 : ∑ α : UpperIdx N, ‖s α‖ *
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ ≤
            ∑ α : UpperIdx N, ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ :=
          Finset.sum_le_sum fun α _ => mul_le_of_le_one_left (hint0 α) (hs1 α)
        have hH := hHigh k (Finset.mem_Icc.2 ⟨hk4g, hk4'⟩)
        calc (N : ℝ) ^ (-(k : ℝ) / 2) * _ ≤ (N : ℝ) ^ (-(k : ℝ) / 2) *
              ∑ α : UpperIdx N, ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) k‖ :=
              mul_le_mul_of_nonneg_left (hgen.trans hs4) hNk0
          _ ≤ Kh * (b + Φθ) := hH
          _ ≤ Kb * (b + X + Φθ) := by
              have : Kh ≤ Kb := by simp only [hKb]; linarith
              exact mul_le_mul this (by linarith) (by linarith) hKb0
    have hBnn : 0 ≤ Kb * (b + X + Φθ) := mul_nonneg hKb0 (by linarith)
    have hzt := hZ s k (Kb * (b + X + Φθ)) hs1 hBnn hk2 hk4' hB
    -- the tail
    have htail : ∑ j ∈ Finset.Icc (k + 2) (4 * p), (N : ℝ) ^ (-(j : ℝ) / 2) *
        ∑ α : UpperIdx N, ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
          ‖fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) j‖ ≤ 4 * p * (Kh * (b + Φθ)) := by
      calc _ ≤ ∑ _j ∈ Finset.Icc (k + 2) (4 * p), Kh * (b + Φθ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
            exact hHigh j (Finset.mem_Icc.2 ⟨by omega, hj2⟩)
        _ = ((Finset.Icc (k + 2) (4 * p)).card : ℝ) * (Kh * (b + Φθ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * p * (Kh * (b + Φθ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [Nat.card_Icc]
            have : 4 * p + 1 - (k + 2) ≤ 4 * p := by omega
            exact_mod_cast this
    have hsum_eq : ∑ α : UpperIdx N, d α k * Z α k =
        ((c k * (N : ℝ) ^ (-(k : ℝ) / 2) : ℝ) : ℂ) *
          ∑ α : UpperIdx N, (s α : ℂ) *
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              fCoeff p (resCoeffW A (Wupd (ofUpper ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hds α, mul_assoc]
      rfl
    rw [hsum_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    calc c k * (N : ℝ) ^ (-(k : ℝ) / 2) * ‖_‖
        = c k * ((N : ℝ) ^ (-(k : ℝ) / 2) * ‖∑ α : UpperIdx N, (s α : ℂ) *
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              fCoeff p (resCoeffW A (Wupd (ofUpper ω) α.1.1 α.1.2 0) z v α.1.1 α.1.2) k‖) := by
          ring
      _ ≤ c k * (Kz * (Kb * (b + X + Φθ) + (N : ℝ) ^ δ * Ψ ^ p +
            4 * p * (Kh * (b + Φθ)))) := by
          refine mul_le_mul_of_nonneg_left (hzt.trans ?_) (hck.le)
          refine mul_le_mul_of_nonneg_left ?_ hKz
          have := htail
          linarith
      _ ≤ c k * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) := by
          have h1 : Kb * (b + X + Φθ) + (N : ℝ) ^ δ * Ψ ^ p + 4 * p * (Kh * (b + Φθ)) ≤
              (Kb + 1 + 4 * p * Kh) * (b + X + Φθ) := by
            have e2 : 4 * p * (Kh * (b + Φθ)) ≤ 4 * p * Kh * (b + X + Φθ) := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have e3 : (Kb + 1 + 4 * p * Kh) * (b + X + Φθ) =
                Kb * (b + X + Φθ) + (b + X + Φθ) + 4 * p * Kh * (b + X + Φθ) := by ring
            rw [e3]
            linarith [hNδb]
          have h2 := mul_le_mul_of_nonneg_left h1 hKz
          have h3 := mul_le_mul_of_nonneg_left h2 hck.le
          linarith
  -- the remainders
  have hrem : ‖∑ α : UpperIdx N, (R α true - R α false)‖ ≤ 4 * b := by
    have h1 : ∀ α, ‖R α true - R α false‖ ≤ 4 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) :=
      fun α => (norm_sub_le _ _).trans (by linarith [hRb α true, hRb α false])
    have h2 : (N : ℝ) ^ 2 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) = (τ / N) ^ p := by
      rw [div_pow, show (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      rw [show (N : ℝ) ^ ((2 : ℕ) : ℝ) * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) =
          τ ^ p * ((N : ℝ) ^ ((2 : ℕ) : ℝ) * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) by ring,
        ← Real.rpow_add hNp]
      rw [show ((2 : ℕ) : ℝ) + ((0 : ℝ) / 2 - 2 - p) = -(p : ℝ) by push_cast; ring,
        Real.rpow_neg hNp.le, Real.rpow_natCast]
      ring
    have h3 : (τ / N) ^ p ≤ b := (pow_le_pow_left₀ (by positivity) hΨ p).trans hΨb
    calc ‖∑ α : UpperIdx N, (R α true - R α false)‖
        ≤ ∑ α : UpperIdx N, ‖R α true - R α false‖ := norm_sum_le _ _
      _ ≤ ∑ _α : UpperIdx N, 4 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p)) :=
          Finset.sum_le_sum fun α _ => h1 α
      _ = (Fintype.card (UpperIdx N) : ℝ) * (4 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ 2 * (4 * (τ ^ p * (N : ℝ) ^ ((0 : ℝ) / 2 - 2 - p))) :=
          mul_le_mul_of_nonneg_right (cmp_card_upper N) (by positivity)
      _ = 4 * (τ / N) ^ p := by rw [← h2]; ring
      _ ≤ 4 * b := by linarith
  -- assembly
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hder]
  have hsumk : ‖∑ k ∈ Finset.Ico 2 (4 * p + 1), ∑ α : UpperIdx N, d α k * Z α k‖ ≤
      Csum * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) := by
    calc _ ≤ ∑ k ∈ Finset.Ico 2 (4 * p + 1), ‖∑ α : UpperIdx N, d α k * Z α k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico 2 (4 * p + 1), c k * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) :=
          Finset.sum_le_sum hord
      _ = (∑ k ∈ Finset.Ico 2 (4 * p + 1), c k) * (Kz * (Kb + 1 + 4 * p * Kh)) *
            (b + X + Φθ) := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ Csum * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          rw [hCsum]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2)
            (fun k _ _ => zero_le_one.trans (hc1 k))
  calc _ ≤ ‖∑ k ∈ Finset.Ico 2 (4 * p + 1), ∑ α : UpperIdx N, d α k * Z α k‖ +
        ‖∑ α : UpperIdx N, (R α true - R α false)‖ := norm_add_le _ _
    _ ≤ Csum * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) + 4 * b := add_le_add hsumk hrem
    _ ≤ (Csum * Kz * (Kb + 1 + 4 * p * Kh) + 4) * (b + X + Φθ) := by
        have e : (Csum * Kz * (Kb + 1 + 4 * p * Kh) + 4) * (b + X + Φθ) =
            Csum * (Kz * (Kb + 1 + 4 * p * Kh)) * (b + X + Φθ) + 4 * (b + X + Φθ) := by ring
        rw [e]
        linarith


/-! ## The Gaussian start and the moment bound by Grönwall -/

private lemma cmp_le_rpow' {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) {N : ℕ}
    (h : ⌈Q ^ a⁻¹⌉₊ ≤ N) : Q ≤ (N : ℝ) ^ a := by
  have h1 : Q ^ a⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  calc Q = (Q ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hQ ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hQ _) h1 ha.le

private lemma cmp_measurable_goeW (N : ℕ) : Measurable (goeW N) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => (isGOE_goeW N).measurable i j

/-- A moment bound from stochastic domination and a deterministic bound:
`E ξ^p ≤ (N^ε ζ)^p + M^p N^{−D}`. -/
private lemma cmp_moment_of_dom {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
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

/-- The Gaussian start: the anisotropic law for `(goeW N, A, S)` at `(δ, 2p + 2)` gives
`E F_v^p(W^Gauss) ≤ (N^{C₀δ} Ψ)^p` on `S`. -/
private lemma cmp_goe_start (τ : ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hp2 : 2 ≤ p) (hδ : 0 < δ)
    (hC₀ : 30 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ), WigSetting τ N A S →
      AnisotropicLawWAt N δ (2 * p + 2) A (goeW N) S →
      ∀ z ∈ S, ∀ v : Fin N → ℝ, testNorm v = 1 →
        ∫ ω, FvW A (goeW N ω) z v ^ p ≤ ((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have he : 0 < (C₀ - 1) * δ * p := by
    have : 0 < C₀ - 1 := by linarith
    positivity
  refine ⟨max (max 1 ⌈τ⁻¹⌉₊) (max ⌈(2 / τ) ^ p⌉₊ ⌈(2 : ℝ) ^ ((C₀ - 1) * δ * p)⁻¹⌉₊), ?_⟩
  intro N hN A S hset hG z hzS v hv
  have hN1 : 1 ≤ N := by omega
  have hNτ : ⌈τ⁻¹⌉₊ ≤ N := by omega
  have hN2τ : ⌈(2 / τ) ^ p⌉₊ ≤ N := by omega
  have hN2 : ⌈(2 : ℝ) ^ ((C₀ - 1) * δ * p)⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hτN : τ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNτ)
  have h2τN : (2 / τ) ^ p ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN2τ)
  have h2N : (2 : ℝ) ≤ (N : ℝ) ^ ((C₀ - 1) * δ * p) := cmp_le_rpow' (by norm_num) he hN2
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have hη0 : 0 < z.im := hzD.1
  have hηN : z.im⁻¹ ≤ N := cmp_im_inv_le hN1 hτ hzD
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨ : τ / N ≤ Ψ := cmp_psi_ge hN1 hτ _ hzD
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨ
  have hdom := hG z hzS v v
  simp only [hv, mul_one] at hdom
  have hmom := cmp_moment_of_dom (ξ := fun ω => FvW A (goeW N ω) z v) (ε := δ)
    (D := 2 * p + 2) (ζ := Ψ) (M := z.im⁻¹ + τ⁻¹) p
    ((cmp_measurable_Fv A z v).comp (cmp_measurable_goeW N)) (fun ω => norm_nonneg _)
    (fun ω => cmp_Fv_le hτ hset.symmA ((isGOE_goeW N).symm ω) hset.standing hzS hη0 hv)
    hΨ0 (add_nonneg (inv_nonneg.2 hη0.le) (inv_nonneg.2 hτ.le)) hN1 hdom
  refine hmom.trans ?_
  -- the deterministic part
  have hM : z.im⁻¹ + τ⁻¹ ≤ 2 * N := by linarith
  have hM0 : 0 ≤ z.im⁻¹ + τ⁻¹ := by positivity
  have hD : (N : ℝ) ^ (-((2 : ℝ) * p + 2)) = ((N : ℝ) ^ (2 * p + 2))⁻¹ := by
    rw [Real.rpow_neg hNp.le]
    congr 1
    rw [show (2 : ℝ) * p + 2 = ((2 * p + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have htail : (z.im⁻¹ + τ⁻¹) ^ p * (N : ℝ) ^ (-((2 : ℝ) * p + 2)) ≤ Ψ ^ p := by
    rw [hD]
    have h1 : (z.im⁻¹ + τ⁻¹) ^ p ≤ (2 * N) ^ p := pow_le_pow_left₀ hM0 hM p
    have h2 : (τ / N) ^ p ≤ Ψ ^ p := pow_le_pow_left₀ (by positivity) hΨ p
    have hNpow : (0 : ℝ) < (N : ℝ) ^ (2 * p + 2) := by positivity
    have h3 : (2 * (N : ℝ)) ^ p * ((N : ℝ) ^ (2 * p + 2))⁻¹ ≤ (τ / N) ^ p := by
      rw [mul_inv_le_iff₀ hNpow, div_pow, mul_pow]
      have h2p : (2 : ℝ) ^ p ≤ τ ^ p * N := by
        have : (2 / τ) ^ p * τ ^ p = (2 : ℝ) ^ p := by
          rw [← mul_pow, div_mul_cancel₀ _ hτ.ne']
        nlinarith [pow_pos hτ p]
      have e : τ ^ p / (N : ℝ) ^ p * (N : ℝ) ^ (2 * p + 2) =
          τ ^ p * (N : ℝ) ^ p * ((N : ℝ) * N) := by
        rw [pow_add, pow_mul]
        field_simp
        ring
      rw [e]
      have hNp1 : (N : ℝ) ≤ (N : ℝ) * N := le_mul_of_one_le_left hNp.le hN1r
      have : (2 : ℝ) ^ p * (N : ℝ) ^ p ≤ τ ^ p * N * (N : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right h2p (by positivity)
      have : τ ^ p * N * (N : ℝ) ^ p ≤ τ ^ p * (N : ℝ) ^ p * ((N : ℝ) * N) := by
        have := mul_le_mul_of_nonneg_left hNp1 (by positivity : (0 : ℝ) ≤ τ ^ p * (N : ℝ) ^ p)
        nlinarith
      linarith
    calc (z.im⁻¹ + τ⁻¹) ^ p * ((N : ℝ) ^ (2 * p + 2))⁻¹
        ≤ (2 * (N : ℝ)) ^ p * ((N : ℝ) ^ (2 * p + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (τ / N) ^ p := h3
      _ ≤ Ψ ^ p := h2
  -- the main part
  have hpow : ((N : ℝ) ^ (C₀ * δ) * Ψ) ^ p = (N : ℝ) ^ (C₀ * δ * p) * Ψ ^ p := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (C₀ * δ)), ← Real.rpow_mul hNp.le]
  have hpow1 : ((N : ℝ) ^ δ * Ψ) ^ p = (N : ℝ) ^ (δ * p) * Ψ ^ p := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ δ), ← Real.rpow_mul hNp.le]
  have hsplit : (N : ℝ) ^ (C₀ * δ * p) = (N : ℝ) ^ (δ * p) * (N : ℝ) ^ ((C₀ - 1) * δ * p) := by
    rw [← Real.rpow_add hNp]
    ring_nf
  rw [hpow, hpow1, hsplit]
  have hA0 : 1 ≤ (N : ℝ) ^ (δ * p) := Real.one_le_rpow hN1r (by positivity)
  have hP0 : 0 ≤ Ψ ^ p := pow_nonneg hΨ0 p
  have : 2 * (N : ℝ) ^ (δ * p) ≤ (N : ℝ) ^ (δ * p) * (N : ℝ) ^ ((C₀ - 1) * δ * p) := by
    nlinarith
  nlinarith

/-- Integrability of `F_v^p ∘ ofUpper` under every probability measure. -/
private lemma cmp_integrable_Fp {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S) {z : ℂ} (hz : z ∈ S)
    (hzim : 0 < z.im) {v : Fin N → ℝ} (hv : testNorm v = 1) (p : ℕ)
    (μ : Measure (UpperIdx N → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => FvW A (ofUpper x) z v ^ p) μ := by
  refine Integrable.of_bound
    (((cmp_measurable_Fv A z v).comp cmp_measurable_ofUpper).pow_const p).aestronglyMeasurable
    ((z.im⁻¹ + τ⁻¹) ^ p) (ae_of_all _ fun x => ?_)
  have h0 : 0 ≤ FvW A (ofUpper x) z v := norm_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg h0 p)]
  exact pow_le_pow_left₀ h0 (cmp_Fv_le hτ hA (cmp_ofUpper_symm x) hS hz hzim hv) p

/-- The moment bound of Lemma 12.7 integrated by Grönwall over `θ`: from (A_{m−1}) for a class
`Q` containing the interpolants and the pair matrices, the Gaussian start and a bound on the
third-order term, `E F_v^p(W) ≤ K (b + X)` with `b = (N^{C₀δ} Ψ)^p`. -/
private lemma cmp_core (τ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ K3 : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4)
    (hK3 : 0 ≤ K3) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (Q : ModelClassW N) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PropAW N (momMaxW C) Q A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      AnisotropicLawWAt N δ (2 * p + 2) A (goeW N) S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1,
        Q (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper) →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ α : UpperIdx N,
        Q (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α (entryLawW W α))) ofUpper ∧
        Q (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α (goeLaw N α))) ofUpper) →
      ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 → ∀ X : ℝ, 0 ≤ X →
      ((∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0) ∨
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ s : UpperIdx N → ℂ, (∀ α, ‖s α‖ ≤ 1) →
          (N : ℝ) ^ (-(3 : ℝ) / 2) * ‖∑ α : UpperIdx N, s α *
            ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
              fCoeff p (resCoeffW A (ofUpper ω) z v α.1.1 α.1.2) 3‖ ≤
            K3 * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p + X +
              ∫ ω : InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W),
                FvW A (ofUpper ω) z v ^ p)) →
      ∫ ω, FvW A (W ω) z v ^ p ≤ Kc * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p + X) := by
  obtain ⟨K', hK', Nd, hd⟩ := cmp_deriv_bound τ C p C₀ δ K3 hτ hτ1 hp hp2 hδ hC₀ hC₀δ hK3
  obtain ⟨Ng, hg⟩ := cmp_goe_start τ p C₀ δ hτ hp2 hδ hC₀
  refine ⟨2 * Real.exp K', by positivity, max (max Nd Ng) 1, ?_⟩
  intro N hN A S Q m hset hm hPA hG Ω _ _ W hW hQ1 hQ2 z hz v hv X hX h3
  have hNd : Nd ≤ N := by omega
  have hNg : Ng ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have hη0 : 0 < z.im := hzD.1
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := cmp_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := cmp_entryLawW_prob hW.measurable
  set Ψ := PsiW (specOf A) z with hΨdef
  have hΨ : τ / N ≤ Ψ := cmp_psi_ge hN1 hτ _ hzD
  have hΨ0 : 0 ≤ Ψ := le_trans (by positivity) hΨ
  set b : ℝ := ((N : ℝ) ^ (C₀ * δ) * Ψ) ^ p with hb
  have hb0 : 0 ≤ b := by positivity
  set F : (UpperIdx N → ℝ) → ℝ := fun x => FvW A (ofUpper x) z v ^ p with hF
  have hFm : Measurable F :=
    ((cmp_measurable_Fv A z v).comp cmp_measurable_ofUpper).pow_const p
  have hint : ∀ u, Integrable F (vertexLaw (goeLaw N) (entryLawW W) u) := by
    intro u
    have : ∀ α, IsProbabilityMeasure (if u α then entryLawW W α else goeLaw N α) := by
      intro α; split <;> infer_instance
    have : IsProbabilityMeasure (vertexLaw (goeLaw N) (entryLawW W) u) := by
      unfold vertexLaw; infer_instance
    exact cmp_integrable_Fp hτ hset.symmA hset.standing hzS hη0 hv p _
  set Φ := interpPoly (goeLaw N) (entryLawW W) F with hΦ
  set Φ' : ℝ → ℝ := fun θ => ∑ α : UpperIdx N,
      ((∫ x, F x ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (entryLawW W α))) -
        ∫ x, F x ∂(interpLawAt θ (goeLaw N) (entryLawW W) α (goeLaw N α))) with hΦ'
  have hΦeq : ∀ θ ∈ Set.Icc (0 : ℝ) 1, Φ θ = ∫ x, F x ∂(interpLaw θ (goeLaw N) (entryLawW W)) :=
    fun θ hθ => (integral_interpLaw_eq_interpPoly hθ.1 hθ.2 hFm hint).symm
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ (Φ' θ) θ :=
    fun θ hθ => hasDerivAt_interpPoly hθ.1 hθ.2 hFm hint
  -- `Φ(0) ≤ b`
  have h0 : Φ 0 ≤ b + X := by
    rw [hΦeq 0 ⟨le_rfl, zero_le_one⟩, cmp_interpLaw_zero]
    have hgl : goeLaw N = entryLawW (goeW N) := funext fun α => (cmp_entryLawW_goeW N α).symm
    rw [hgl, cmp_integral_pi_entryLaw (F := fun M => FvW A M z v ^ p)
      ((isGOE_goeW N).classEntries hN1) hFm]
    have := hg N hNg A S hset hG z hzS v hv
    linarith
  -- Grönwall
  have hgr := gronwall_affine (Φ := Φ) (Φ' := Φ') (K := K') (a := b + X) hK'
    (by linarith)
    (fun θ hθ => (hderiv θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ => hderiv θ ⟨hθ.1, hθ.2.le⟩)
    (fun θ hθ => by
      have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1, hθ.2.le⟩
      have h := hd N hNd A S Q m hset hm hPA Ω W hW hQ1 hQ2 z hz v hv X hX h3 θ hθ'
      rw [hΦeq θ hθ']
      exact (le_abs_self _).trans h)
    h0
  -- `Φ(1) = E F_v^p(W)`
  have h1 : ∫ ω, FvW A (W ω) z v ^ p = Φ 1 := by
    rw [hΦeq 1 ⟨zero_le_one, le_rfl⟩, cmp_interpLaw_one]
    exact (cmp_integral_pi_entryLaw (F := fun M => FvW A M z v ^ p) hW hFm).symm
  rw [h1]
  refine hgr.trans ?_
  have := Real.exp_pos K'
  nlinarith


/-! ## Markov's inequality, monotonicity, (C) ⇒ (A), polarization -/

/-- `W ↦ W` is measurable for a matrix with measurable entries. -/
private lemma cmp_measurable_W {Ω : Type*} [MeasureSpace Ω] {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : ∀ i j, Measurable fun ω => W ω i j) : Measurable W :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hW i j

private lemma cmp_psi_pos {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < PsiW a z := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  unfold PsiW
  have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  linarith [Real.sqrt_nonneg ((mW a z).im / (N * z.im))]

/-- Markov's inequality turns a moment bound into (C_m). -/
private lemma cmp_propC_of_moment {N : ℕ} {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    {P : ModelClassW N} {C : ℕ → ℝ} {C₀ δ ε ε' D Kp : ℝ} {m p : ℕ}
    (hset : WigSetting τ N A S) (hN : 1 ≤ N) (hp : D ≤ (ε' - ε) * p)
    (hK : Kp ≤ (N : ℝ) ^ (p * ε))
    (hmom : ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries C N W → P Ω W →
      ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
        ∫ ω, FvW A (W ω) z v ^ p ≤ Kp * ((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p) :
    PropCW N C P A S C₀ δ m ε' D := by
  intro Ω _ _ W hW hP z hz v hv
  have hzS : z ∈ S := hz.1
  have hzim : 0 < z.im := (hset.domain.1 hzS).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 0 < (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z :=
    mul_pos (Real.rpow_pos_of_pos hNpos _) (cmp_psi_pos hN _ hzim)
  have hint : Integrable fun ω => FvW A (W ω) z v ^ p := by
    refine Integrable.of_bound
      (((cmp_measurable_Fv A z v).comp (cmp_measurable_W hW.measurable)).pow_const p
        ).aestronglyMeasurable ((z.im⁻¹ + τ⁻¹) ^ p) (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ FvW A (W ω) z v := norm_nonneg _
    rw [Real.norm_of_nonneg (pow_nonneg h0 p)]
    exact pow_le_pow_left₀ h0
      (cmp_Fv_le hset.pos hset.symmA (hW.symm ω) hset.standing hzS hzim hv) p
  have hmom' := hmom Ω W hW hP z hz v hv
  refine DomAt.of_moment (ε := ε) p hN hp (fun ω => norm_nonneg _) hb hint (hmom'.trans ?_)
  have e : ((N : ℝ) ^ ε * ((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z)) ^ p =
      (N : ℝ) ^ ((p : ℝ) * ε) * ((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ ε), ← Real.rpow_mul hNpos.le, mul_comm ε]
  rw [e]
  exact mul_le_mul_of_nonneg_right hK (pow_nonneg hb.le p)

/-- Monotonicity of `DomAt` in `ε` and `D`. -/
private lemma cmp_domAt_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N) {ε ε' D D' : ℝ}
    {ξ ζ : Ω → ℝ} (hζ : ∀ ω, 0 ≤ ζ ω) (hε : ε ≤ ε') (hD : D' ≤ D) (h : DomAt N ε D ξ ζ) :
    DomAt N ε' D' ξ ζ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold DomAt at h ⊢
  refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN1 hε) (hζ ω)) hω

private lemma cmp_mW_im_nonneg {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (mW a z).im := (mW_spec hN a hz).1.le

/-- Monotonicity of (A_m) in `ε` and `D`. -/
private lemma cmp_propA_mono {N : ℕ} {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    {P : ModelClassW N} {C : ℕ → ℝ} {C₀ δ ε ε' D D' : ℝ} {m : ℕ} (hset : WigSetting τ N A S)
    (hN : 1 ≤ N) (hε : ε ≤ ε') (hD : D' ≤ D) (h : PropAW N C P A S C₀ δ m ε D) :
    PropAW N C P A S C₀ δ m ε' D' := by
  intro Ω _ _ W hW hP z hz v hv
  have hzim : 0 < z.im := (hset.domain.1 hz.1).1
  refine cmp_domAt_mono hN (fun _ => ?_) hε hD (h Ω W hW hP z hz v hv)
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have := cmp_mW_im_nonneg hN (specOf A) hzim
  have := (cmp_psi_pos hN (specOf A) hzim).le
  positivity

/-- Monotonicity of the anisotropic law in `D`. -/
private lemma cmp_aniso_mono {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℝ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ} {ε D D' : ℝ}
    (hD : D' ≤ D) (h : AnisotropicLawWAt N ε D A W S) : AnisotropicLawWAt N ε D' A W S := by
  intro z hz v w
  have h1 := h z hz v w
  unfold DomAt at h1 ⊢
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-! ### `Im Π_{vv} ≤ τ⁻²(1 + κ⁻¹) Im m` -/

private lemma cmp_eig_decompH {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsHermitian) :
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

private lemma cmp_resolvent_eq {N : ℕ} {M U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ} {w : ℂ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hMU : M = U * diagonal l * Uᵀ)
    (hne : ∀ k, (l k : ℂ) - w ≠ 0) :
    (cplx M - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (cplx U) * diagonal (fun k => ((l k : ℂ) - w)⁻¹) * (cplx U)ᵀ :=
  Matrix.inv_eq_right_inv (cmp_right_inv hUU hUU' hMU hne)

private lemma cmp_ent_sandwich_sq {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℂ)
    (v : Fin N → ℝ) :
    ent (cplx U * diagonal d * (cplx U)ᵀ) v v = ∑ k, d k * ((((Uᵀ *ᵥ v) k) ^ 2 : ℝ) : ℂ) := by
  rw [cmp_ent_sandwich]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  ring

/-- `Im Π_{vv} ≤ τ⁻² (1 + κ⁻¹) Im m` for `|v| = 1`, `κ = (3τ⁻¹ + 1)⁻²`, under the standing bound,
on `𝐃^W(τ, N)`. -/
private lemma cmp_im_piW_le {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hnA : ‖A‖ ≤ τ⁻¹) {S : Set ℂ} (hS : StandingBoundW τ (specOf A) S)
    {z : ℂ} (hz : z ∈ S) (hzD : z ∈ domW τ N) {v : Fin N → ℝ} (hv : testNorm v = 1) :
    (ent (piW A z) v v).im ≤ τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) * (mW (specOf A) z).im := by
  obtain ⟨hzim, hzE, -, hzη⟩ := hzD
  set m := mW (specOf A) z with hm
  have ha : ∀ i, |specOf A i| ≤ τ⁻¹ := fun i => (abs_specOf_le_norm hA i).trans hnA
  have hmge : ((3 * τ⁻¹ + 1) ^ 2)⁻¹ * z.im ≤ m.im := im_mW_ge hN hτ ha hzim hzE hzη
  have hm0 : 0 < m.im := (mW_spec hN (specOf A) hzim).1
  obtain ⟨U, hUU, hUU', hAU⟩ := cmp_eig_decompH hA
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
    cmp_resolvent_eq hUU hUU' hAU hne
  rw [hpi, cmp_ent_sandwich_sq, Complex.im_sum]
  have hsq : ∑ k, ((Uᵀ *ᵥ v) k) ^ 2 = 1 := by
    have h := cmp_testNorm_orth (Q := Uᵀ) (by simpa using hUU) v
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
private lemma cmp_propA_of_propC {N : ℕ} {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    {P : ModelClassW N} {C : ℕ → ℝ} {C₀ δ ε D : ℝ} {m : ℕ} (hset : WigSetting τ N A S)
    (hN : 1 ≤ N) (hε : τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) ≤ (N : ℝ) ^ ε)
    (h : PropCW N C P A S C₀ δ m ε D) : PropAW N C P A S C₀ δ m ε D := by
  intro Ω _ _ W hW hP z hz v hv
  have hzS : z ∈ S := hz.1
  have hzD : z ∈ domW τ N := hset.domain.1 hzS
  have hzim : 0 < z.im := hzD.1
  have hm : 0 < (mW (specOf A) z).im := (mW_spec hN (specOf A) hzim).1
  have hPi := cmp_im_piW_le hN hset.pos hset.symmA hset.normA hset.standing hzS hzD hv
  have hK : τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) * (mW (specOf A) z).im ≤
      (N : ℝ) ^ ε * (mW (specOf A) z).im := mul_le_mul_of_nonneg_right hε hm.le
  have hC := h Ω W hW hP z hz v hv
  unfold ODomAt DomAt at hC
  unfold DomAt
  refine le_trans (measure_mono fun ω hω => ?_) hC
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hG : (ent (GW A (W ω) z) v v).im ≤ (ent (piW A z) v v).im +
      ‖ent (GW A (W ω) z - piW A z) v v‖ := by
    rw [cmp_ent_sub]
    have := Complex.im_le_norm (ent (GW A (W ω) z) v v - ent (piW A z) v v)
    simp only [Complex.sub_im] at this
    linarith
  rw [mul_add] at hω
  linarith

/-! ### Polarization -/

private lemma cmp_testBilin_smul_left {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) : testBilin (a • v) B w = a * testBilin v B w := by
  have e : (fun s => (((a • v) s : ℝ) : ℂ)) = (a : ℂ) • fun s => (v s : ℂ) := by
    funext s
    simp
  unfold testBilin
  rw [e, smul_dotProduct, smul_eq_mul]

private lemma cmp_testBilin_smul_right {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ)
    (B : Matrix ι ι ℂ) (w : ι → ℝ) : testBilin v B (a • w) = a * testBilin v B w := by
  have e : (fun s => (((a • w) s : ℝ) : ℂ)) = (a : ℂ) • fun s => (w s : ℂ) := by
    funext s
    simp
  unfold testBilin
  rw [e, mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma cmp_testNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    testNorm v ^ 2 = ∑ s, v s ^ 2 := by
  unfold testNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma cmp_testNorm_smul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    testNorm (a • v) = |a| * testNorm v := by
  unfold testNorm
  have e : ∑ s, (a • v) s ^ 2 = a ^ 2 * ∑ s, v s ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

private lemma cmp_eq_zero_of_testNorm {ι : Type*} [Fintype ι] {v : ι → ℝ}
    (h : testNorm v = 0) : v = 0 := by
  have h2 : ∑ s, v s ^ 2 = 0 := by
    rw [← cmp_testNorm_sq, h]
    ring
  funext s
  have := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (v t)).1 h2 s
    (Finset.mem_univ s)
  simpa using this

/-- From the diagonal bound for unit vectors, `|⟨a, B a⟩| ≤ |a|² N^ε Y` off an event of
probability at most `N^{−(D+1)}`, for every `a`. -/
private lemma cmp_diag_event {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ι : Type*} [Fintype ι]
    {B : Ω → Matrix ι ι ℂ} {ε D Y : ℝ}
    (h : ∀ u : ι → ℝ, testNorm u = 1 →
      DomAt N ε (D + 1) (fun ω => ‖testBilin u (B ω) u‖) (fun _ => Y)) (a : ι → ℝ) :
    ∃ E : Set Ω, ℙ E ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) ∧
      ∀ ω ∉ E, ‖testBilin a (B ω) a‖ ≤ testNorm a ^ 2 * ((N : ℝ) ^ ε * Y) := by
  by_cases ha : testNorm a = 0
  · refine ⟨∅, by simp, fun ω _ => ?_⟩
    have h0 := cmp_eq_zero_of_testNorm ha
    subst h0
    rw [ha]
    simp [testBilin]
  · set u : ι → ℝ := (testNorm a)⁻¹ • a with hu
    have hpos : 0 < testNorm a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
    have hu1 : testNorm u = 1 := by
      rw [hu, cmp_testNorm_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ ha]
    have hau : a = testNorm a • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ ha, one_smul]
    refine ⟨{ω | (N : ℝ) ^ ε * Y < ‖testBilin u (B ω) u‖}, h u hu1, fun ω hω => ?_⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hω
    have e : testBilin a (B ω) a = ((testNorm a ^ 2 : ℝ) : ℂ) * testBilin u (B ω) u := by
      conv_lhs => rw [hau]
      rw [cmp_testBilin_smul_left, cmp_testBilin_smul_right]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hω (sq_nonneg _)

/-- Polarization: the diagonal bounds `|⟨u, B u⟩| ≺ Y` on the unit sphere, for a symmetric `B`,
give `|⟨v, B w⟩| ≺ Y |v| |w|` for all `v, w`, at the cost `D + 1 ↦ D`. -/
private lemma cmp_bilin_of_diag {Ω : Type*} [MeasureSpace Ω] {N : ℕ} {ι : Type*} [Fintype ι]
    {B : Ω → Matrix ι ι ℂ} (hB : ∀ ω, (B ω)ᵀ = B ω) {ε D Y : ℝ} (hN : 2 ≤ N)
    (h : ∀ u : ι → ℝ, testNorm u = 1 →
      DomAt N ε (D + 1) (fun ω => ‖testBilin u (B ω) u‖) (fun _ => Y)) (v w : ι → ℝ) :
    DomAt N ε D (fun ω => ‖testBilin v (B ω) w‖) (fun _ => Y * testNorm v * testNorm w) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold DomAt
  by_cases hv0 : testNorm v = 0
  · have h0 := cmp_eq_zero_of_testNorm hv0
    subst h0
    have he : {ω | (N : ℝ) ^ ε * (Y * testNorm (0 : ι → ℝ) * testNorm w) <
        ‖testBilin 0 (B ω) w‖} = ∅ := by
      ext ω
      simp [testBilin, hv0]
    rw [he, measure_empty]
    simp
  by_cases hw0 : testNorm w = 0
  · have h0 := cmp_eq_zero_of_testNorm hw0
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
    rw [hv', cmp_testNorm_smul, abs_inv, abs_of_pos hvp, inv_mul_cancel₀ hv0]
  have hw1 : testNorm w' = 1 := by
    rw [hw', cmp_testNorm_smul, abs_inv, abs_of_pos hwp, inv_mul_cancel₀ hw0]
  have hvv : v = testNorm v • v' := by rw [hv', smul_smul, mul_inv_cancel₀ hv0, one_smul]
  have hww : w = testNorm w • w' := by rw [hw', smul_smul, mul_inv_cancel₀ hw0, one_smul]
  have hsum : testNorm (v' + w') ^ 2 + testNorm (v' - w') ^ 2 = 4 := by
    have h1 := cmp_testNorm_sq v'
    have h2 := cmp_testNorm_sq w'
    rw [hv1] at h1
    rw [hw1] at h2
    rw [cmp_testNorm_sq, cmp_testNorm_sq, ← Finset.sum_add_distrib]
    have e : ∀ s, (v' + w') s ^ 2 + (v' - w') s ^ 2 = 2 * v' s ^ 2 + 2 * w' s ^ 2 := fun s => by
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← h1, ← h2]
    norm_num
  obtain ⟨Ea, hEa, ha⟩ := cmp_diag_event (B := B) h (v' + w')
  obtain ⟨Eb, hEb, hb⟩ := cmp_diag_event (B := B) h (v' - w')
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
      rw [cmp_testBilin_smul_left, cmp_testBilin_smul_right]
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
private lemma cmp_GW_sub_piW_symm {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
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

/-! ### Level sets and `Ψ` -/

/-- `Ψ^W ≤ 2 N^{−τ/2}` on `𝐃^W(τ, N)`. -/
private lemma cmp_psi_le {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ : 0 < τ) (a : Fin N → ℝ) {z : ℂ}
    (hz : z ∈ domW τ N) : PsiW a z ≤ 2 * (N : ℝ) ^ (-τ / 2) := by
  obtain ⟨h0, -, hηl, -⟩ := hz
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hNη : (N : ℝ) ^ τ ≤ N * z.im := by
    have : (N : ℝ) * (N : ℝ) ^ (-1 + τ) = (N : ℝ) ^ τ := by
      rw [← Real.rpow_one_add' hNp.le (by linarith)]; ring_nf
    rw [← this]
    exact mul_le_mul_of_nonneg_left hηl hNp.le
  have hNτ : 0 < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNp _
  have hm : (mW a z).im < 1 := lt_of_le_of_lt (Complex.im_le_norm _) (norm_mW_lt_one hN a h0)
  have h1 : 1 / ((N : ℝ) * z.im) ≤ (N : ℝ) ^ (-τ / 2) := by
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = (N : ℝ) ^ (-τ / 2) * (N : ℝ) ^ (τ / 2) := by
          rw [← Real.rpow_add hNp, show -τ / 2 + τ / 2 = (0 : ℝ) by ring, Real.rpow_zero]
      _ ≤ (N : ℝ) ^ (-τ / 2) * (N : ℝ) ^ τ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith))
            (Real.rpow_nonneg hNp.le _)
      _ ≤ (N : ℝ) ^ (-τ / 2) * (N * z.im) :=
          mul_le_mul_of_nonneg_left hNη (Real.rpow_nonneg hNp.le _)
  have h2 : √((mW a z).im / (N * z.im)) ≤ (N : ℝ) ^ (-τ / 2) := by
    have e : (N : ℝ) ^ (-τ / 2) = √((N : ℝ) ^ (-τ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]; ring_nf
    rw [e]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity)]
    calc (mW a z).im ≤ 1 := hm.le
      _ = (N : ℝ) ^ (-τ) * (N : ℝ) ^ τ := by
          rw [← Real.rpow_add hNp, show -τ + τ = (0 : ℝ) by ring, Real.rpow_zero]
      _ ≤ (N : ℝ) ^ (-τ) * (N * z.im) :=
          mul_le_mul_of_nonneg_left hNη (Real.rpow_nonneg hNp.le _)
  unfold PsiW
  linarith

/-- `S_m = S_{min(m, m*)}` with `m* = max(1, ⌈(1 − τ)/δ⌉)`, for `S ⊆ 𝐃^W(τ, N)`. -/
private lemma cmp_levelSet_min {N : ℕ} (hN : 1 ≤ N) {τ δ : ℝ} (hδ : 0 < δ) {S : Set ℂ}
    (hS : S ⊆ domW τ N) (m : ℕ) :
    levelSet N δ S m = levelSet N δ S (min m (topLevel τ δ)) := by
  rcases le_total m (topLevel τ δ) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have key : ∀ l : ℕ, topLevel τ δ ≤ l → levelSet N δ S l = S := by
      intro l hl
      ext z
      refine ⟨fun hz => hz.1, fun hz => ⟨hz, ?_⟩⟩
      obtain ⟨-, -, hηl, -⟩ := hS hz
      refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1r ?_) hηl
      have h1 : (1 - τ) / δ ≤ (topLevel τ δ : ℝ) := by
        unfold topLevel
        push_cast
        exact (Nat.le_ceil _).trans (le_max_right _ _)
      have h2 : (topLevel τ δ : ℝ) ≤ l := by exact_mod_cast hl
      have h3 : 1 - τ ≤ δ * l := by
        have := (div_le_iff₀ hδ).1 (h1.trans h2)
        linarith
      linarith
    rw [key m h, key _ le_rfl]


/-! ## Case (a): vanishing third moments -/

private lemma cmp_markovPow_even (δ D : ℝ) : Even (markovPow δ D) :=
  ⟨max 1 ⌈8 * D / δ⌉₊, by unfold markovPow; ring⟩

private lemma cmp_markovPow_two (δ D : ℝ) : 2 ≤ markovPow δ D := by
  unfold markovPow
  have := le_max_left 1 ⌈8 * D / δ⌉₊
  omega

/-- `D ≤ (δ/8 − δ/16) p` for `p = markovPow δ D`. -/
private lemma cmp_markovPow_ge {δ : ℝ} (hδ : 0 < δ) (D : ℝ) :
    D ≤ (δ / 8 - δ / 16) * (markovPow δ D : ℝ) := by
  have hc1 : 8 * D / δ ≤ (⌈8 * D / δ⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈8 * D / δ⌉₊ : ℝ) ≤ (max 1 ⌈8 * D / δ⌉₊ : ℕ) := by
    exact_mod_cast le_max_right _ _
  have hpc : ((markovPow δ D : ℕ) : ℝ) = 2 * ((max 1 ⌈8 * D / δ⌉₊ : ℕ) : ℝ) := by
    unfold markovPow
    push_cast
    ring
  have h8 : 8 * D = (8 * D / δ) * δ := by field_simp
  rw [hpc]
  nlinarith

/-- Case (a) of the induction step: (A_{m−1}) for the class with vanishing third moments at
`(δ/4, dPrev p)` gives (C_m) for that class at `(δ/8, D)`, with `p = markovPow δ D`. -/
private lemma cmp_caseA (τ : ℝ) (C : ℕ → ℝ) (C₀ δ D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ)
    (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (m : ℕ),
      WigSetting τ N A S → 1 ≤ m →
      AnisotropicLawWAt N δ (2 * markovPow δ D + 2) A (goeW N) S →
      PropAW N (momMaxW C) zeroThirdW A S C₀ δ (m - 1) (δ / 4) (dPrev (markovPow δ D)) →
      PropCW N (momMaxW C) zeroThirdW A S C₀ δ m (δ / 8) D := by
  set p := markovPow δ D with hpdef
  have hpE : Even p := cmp_markovPow_even δ D
  have hp2 : 2 ≤ p := cmp_markovPow_two δ D
  obtain ⟨Kc, hKc, Nc, hc⟩ := cmp_core τ C p C₀ δ 0 hτ hτ1 hpE hp2 hδ hC₀ hC₀δ le_rfl
  refine ⟨max (max Nc ⌈Kc ^ (δ / 16)⁻¹⌉₊) 1, fun N hN A S m hset hm hG hA => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNc : Nc ≤ N := by omega
  have hNK : ⌈Kc ^ (δ / 16)⁻¹⌉₊ ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine cmp_propC_of_moment (ε := δ / 16) (Kp := Kc) hset hN1 (cmp_markovPow_ge hδ D) ?_ ?_
  · have hK := cmp_le_rpow' hKc (by positivity : (0 : ℝ) < δ / 16) hNK
    refine hK.trans (Real.rpow_le_rpow_of_exponent_le hNr ?_)
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    nlinarith
  · intro Ω _ _ W hW hP z hz v hv
    have : ∀ β, IsProbabilityMeasure (goeLaw N β) := cmp_goeLaw_prob N
    have : ∀ β, IsProbabilityMeasure (entryLawW W β) := cmp_entryLawW_prob hW.measurable
    have h3 : ∀ α : UpperIdx N, ∫ y, y ^ 3 ∂(entryLawW W α) = 0 :=
      cmp_entryLawW_third hW.measurable hP
    have hQ1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        zeroThirdW (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper :=
      fun θ hθ => cmp_zeroThird_interp hN1 hW hP hθ.1 hθ.2
    have hQ2 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ α : UpperIdx N,
        zeroThirdW (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α (entryLawW W α)))
          ofUpper ∧
        zeroThirdW (CmpPi N (cmpPairLaw θ (goeLaw N) (entryLawW W) α (goeLaw N α))) ofUpper := by
      intro θ hθ α
      exact ⟨cmp_zeroThird_pair hN1 hW hP hθ.1 hθ.2 α (entryLawW W α) (h3 α),
        cmp_zeroThird_pair hN1 hW hP hθ.1 hθ.2 α (goeLaw N α) (cmp_integral_cube_gaussianReal _)⟩
    have := hc N hNc A S zeroThirdW m hset hm hA hG Ω W hW hQ1 hQ2 z hz v hv 0 le_rfl
      (Or.inl h3)
    simpa using this

/-! ## Case (b): one step of the `Φ`-iteration -/

/-- One step of the `Φ`-iteration (Lemma 12.7 with (Wig_self_improv)): an a priori bound
`|⟨v, (G − Π) w⟩| ≺ N^{2δ} Φ |v||w|` for the whole class gives
`E F_v^p ≤ K((N^{C₀δ} Ψ)^p + (N^{−c₀/2} Φ)^p)`. -/
private lemma cmp_stepB (τ c₀ : ℝ) (C : ℕ → ℝ) (p : ℕ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc₀ : 0 < c₀) (hp : Even p) (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀)
    (hC₀δ : C₀ * δ ≤ τ / 4) (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ)
      (m : ℕ), WigSetting τ N A S → 1 ≤ m → PsiSmallW c₀ (specOf A) S →
      PropAW N (momMaxW C) allModelsW A S C₀ δ (m - 1) (δ / 4) (dPrev p) →
      AnisotropicLawWAt N δ (2 * p + 2) A (goeW N) S →
      ∀ Φf : ℂ → ℝ, (∀ z ∈ levelSet N δ S m, 0 ≤ Φf z ∧ Φf z ≤ 1 + τ⁻¹) →
      (∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
        (W' : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W' →
        ∀ z ∈ levelSet N δ S m, ∀ v w : Fin N → ℝ, DomAt N (δ / 4) (dPrev p)
          (fun ω => ‖testBilin v (GW A (W' ω) z - piW A z) w‖)
          (fun _ => (N : ℝ) ^ (2 * δ) * Φf z * testNorm v * testNorm w)) →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
          ∫ ω, FvW A (W ω) z v ^ p ≤
            Kc * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p +
              ((N : ℝ) ^ (-c₀ / 2) * Φf z) ^ p) := by
  obtain ⟨K3, hK3, N3, h3⟩ := wig_coeff_three τ c₀ (momMaxW C) p C₀ δ (δ / 4) (dPrev p) hτ hτ1
    hc₀ hp hp2 hδ hC₀ hC₀δ hδc le_rfl
  obtain ⟨Kc, hKc, Nc, hc⟩ := cmp_core τ C p C₀ δ K3 hτ hτ1 hp hp2 hδ hC₀ hC₀δ hK3
  refine ⟨Kc, hKc, max (max N3 Nc) 1, ?_⟩
  intro N hN A S m hset hm hPs hPA hG Φf hΦ hB Ω _ _ W hW z hz v hv
  have hN1 : 1 ≤ N := by omega
  have hN3 : N3 ≤ N := by omega
  have hNc : Nc ≤ N := by omega
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hX : 0 ≤ ((N : ℝ) ^ (-c₀ / 2) * Φf z) ^ p :=
    pow_nonneg (mul_nonneg (Real.rpow_nonneg hNp.le _) (hΦ z hz).1) p
  refine hc N hNc A S allModelsW m hset hm hPA hG Ω W hW (fun _ _ => trivial)
    (fun _ _ _ => ⟨trivial, trivial⟩) z hz v hv _ hX (Or.inr fun θ hθ s hs => ?_)
  have : ∀ β, IsProbabilityMeasure (goeLaw N β) := cmp_goeLaw_prob N
  have : ∀ β, IsProbabilityMeasure (entryLawW W β) := cmp_entryLawW_prob hW.measurable
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (goeLaw N β) (entryLawW W β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  have hIP : IsProbabilityMeasure (interpLaw θ (goeLaw N) (entryLawW W)) := by
    unfold interpLaw
    infer_instance
  have : IsProbabilityMeasure
      (ℙ : Measure (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W))) := hIP
  have hWθ := cmp_class_interp hN1 hW hθ.1 hθ.2
  exact h3 N hN3 A S allModelsW m hset hm hPA hPs
    (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ trivial z hz (Φf z)
    (hΦ z hz).1 (hΦ z hz).2
    (hB (InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) ofUpper hWθ z hz) le_rfl v hv s hs

/-- The sequence `Φ₀ = 1`, `Φ_{k+1} = N^{(C₀−2)δ} ψ + N^{−c₀/2−2δ} Φ_k` of the
`Φ`-iteration. -/
private def cmpPhi (N : ℕ) (C₀ δ c₀ ψ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (N : ℝ) ^ ((C₀ - 2) * δ) * ψ + (N : ℝ) ^ (-c₀ / 2 - 2 * δ) * cmpPhi N C₀ δ c₀ ψ k

private lemma cmp_phi_nonneg {N : ℕ} {C₀ δ c₀ ψ : ℝ} (hψ : 0 ≤ ψ) (k : ℕ) :
    0 ≤ cmpPhi N C₀ δ c₀ ψ k := by
  induction k with
  | zero => simp [cmpPhi]
  | succ k ih =>
    simp only [cmpPhi]
    have := Real.rpow_nonneg (Nat.cast_nonneg N) ((C₀ - 2) * δ)
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (-c₀ / 2 - 2 * δ)
    positivity

private lemma cmp_phi_succ_mul {N : ℕ} (hN : 1 ≤ N) (C₀ δ c₀ ψ : ℝ) (k : ℕ) :
    (N : ℝ) ^ (2 * δ) * cmpPhi N C₀ δ c₀ ψ (k + 1) =
      (N : ℝ) ^ (C₀ * δ) * ψ + (N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ ψ k := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  simp only [cmpPhi]
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
  congr 3 <;> ring

/-- `Φ_k ≤ k N^{(C₀−2)δ} ψ + N^{−k c₀/2}`. -/
private lemma cmp_phi_le {N : ℕ} (hN : 1 ≤ N) {C₀ δ c₀ ψ : ℝ} (hδ : 0 ≤ δ) (hc₀ : 0 ≤ c₀)
    (hψ : 0 ≤ ψ) (k : ℕ) :
    cmpPhi N C₀ δ c₀ ψ k ≤ k * ((N : ℝ) ^ ((C₀ - 2) * δ) * ψ) + (N : ℝ) ^ (-(k * c₀ / 2)) := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  induction k with
  | zero => simp [cmpPhi]
  | succ k ih =>
    simp only [cmpPhi]
    have hr : (N : ℝ) ^ (-c₀ / 2 - 2 * δ) ≤ (N : ℝ) ^ (-c₀ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have hr1 : (N : ℝ) ^ (-c₀ / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
    have hr0 : 0 ≤ (N : ℝ) ^ (-c₀ / 2 - 2 * δ) := Real.rpow_nonneg hNp.le _
    have hy0 : 0 ≤ (N : ℝ) ^ ((C₀ - 2) * δ) * ψ := mul_nonneg (Real.rpow_nonneg hNp.le _) hψ
    have hφ0 := cmp_phi_nonneg (N := N) (C₀ := C₀) (δ := δ) (c₀ := c₀) hψ k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (N : ℝ) ^ (-c₀ / 2 - 2 * δ) * cmpPhi N C₀ δ c₀ ψ k ≤
        (N : ℝ) ^ (-c₀ / 2) * (k * ((N : ℝ) ^ ((C₀ - 2) * δ) * ψ) +
          (N : ℝ) ^ (-(k * c₀ / 2))) :=
      mul_le_mul hr ih hφ0 (Real.rpow_nonneg hNp.le _)
    have h2 : (N : ℝ) ^ (-c₀ / 2) * (N : ℝ) ^ (-(k * c₀ / 2)) =
        (N : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * c₀ / 2)) := by
      rw [← Real.rpow_add hNp]
      congr 1
      push_cast
      ring
    have h3 : (N : ℝ) ^ (-c₀ / 2) * (k * ((N : ℝ) ^ ((C₀ - 2) * δ) * ψ)) ≤
        k * ((N : ℝ) ^ ((C₀ - 2) * δ) * ψ) := by
      have := mul_le_mul_of_nonneg_right hr1 (mul_nonneg hk0 hy0)
      linarith
    rw [mul_add, h2] at h1
    have e : (((k + 1 : ℕ) : ℝ)) * ((N : ℝ) ^ ((C₀ - 2) * δ) * ψ) =
        k * ((N : ℝ) ^ ((C₀ - 2) * δ) * ψ) + (N : ℝ) ^ ((C₀ - 2) * δ) * ψ := by
      push_cast; ring
    rw [e]
    linarith

/-- `Φ_k ≤ 1 + τ⁻¹` once `N^{τ/4} ≥ 2k`, on `𝐃^W(τ, N)` with `C₀ δ ≤ τ/4`. -/
private lemma cmp_phi_le_one {N : ℕ} (hN : 1 ≤ N) {τ C₀ δ c₀ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hc₀ : 0 ≤ c₀) (hC₀δ : C₀ * δ ≤ τ / 4) (a : Fin N → ℝ) {z : ℂ}
    (hz : z ∈ domW τ N) (k : ℕ)
    (hk : 2 * (k : ℝ) ≤ (N : ℝ) ^ (τ / 4)) :
    cmpPhi N C₀ δ c₀ (PsiW a z) k ≤ 1 + τ⁻¹ := by
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hΨ0 : 0 ≤ PsiW a z := (cmp_psi_pos hN a hz.1).le
  have h1 := cmp_phi_le hN (C₀ := C₀) hδ.le hc₀ hΨ0 k
  have h2 : (N : ℝ) ^ (-(k * c₀ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by have := Nat.cast_nonneg (α := ℝ) k; nlinarith)
  have hΨ := cmp_psi_le hN hτ a hz
  have h3 : (N : ℝ) ^ ((C₀ - 2) * δ) * PsiW a z ≤ 2 * (N : ℝ) ^ (-(τ / 4)) := by
    have e1 : (N : ℝ) ^ ((C₀ - 2) * δ) ≤ (N : ℝ) ^ (τ / 4) :=
      Real.rpow_le_rpow_of_exponent_le hN1r (by nlinarith)
    calc (N : ℝ) ^ ((C₀ - 2) * δ) * PsiW a z ≤ (N : ℝ) ^ (τ / 4) * (2 * (N : ℝ) ^ (-τ / 2)) :=
          mul_le_mul e1 hΨ hΨ0 (Real.rpow_nonneg hNp.le _)
      _ = 2 * (N : ℝ) ^ (-(τ / 4)) := by
          rw [mul_left_comm, ← Real.rpow_add hNp]
          congr 2
          ring
  have h4 : (k : ℝ) * (2 * (N : ℝ) ^ (-(τ / 4))) ≤ 1 := by
    rw [Real.rpow_neg hNp.le]
    have hpos : 0 < (N : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hNp _
    rw [← mul_assoc, mul_comm (k : ℝ) 2, ← div_eq_mul_inv, div_le_one hpos]
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h5 : (k : ℝ) * ((N : ℝ) ^ ((C₀ - 2) * δ) * PsiW a z) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h3 hk0).trans h4
  have : 1 ≤ τ⁻¹ := one_le_inv_iff₀.2 ⟨hτ, hτ1⟩
  linarith


/-! ## Case (b): the `Φ`-iteration, the levels, and the induction step -/

private lemma cmp_integrable_Fv_pow {N : ℕ} {τ : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {S : Set ℂ}
    (hset : WigSetting τ N A S) {C : ℕ → ℝ} {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) {z : ℂ} (hz : z ∈ S) {v : Fin N → ℝ} (hv : testNorm v = 1)
    (p : ℕ) : Integrable fun ω => FvW A (W ω) z v ^ p := by
  have hzim : 0 < z.im := (hset.domain.1 hz).1
  refine Integrable.of_bound
    (((cmp_measurable_Fv A z v).comp (cmp_measurable_W hW.measurable)).pow_const p
      ).aestronglyMeasurable ((z.im⁻¹ + τ⁻¹) ^ p) (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ FvW A (W ω) z v := norm_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg h0 p)]
  exact pow_le_pow_left₀ h0 (cmp_Fv_le hset.pos hset.symmA (hW.symm ω) hset.standing hz hzim hv) p

/-- The `Φ`-iteration: after `k` steps, `E F_v^p ≤ K((N^{C₀δ} Ψ)^p + (N^{−c₀/2} Φ_k)^p)` for
the whole class, from (A_{m−1}) for the whole class and the Gaussian start. -/
private lemma cmp_iter (τ c₀ : ℝ) (C : ℕ → ℝ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc₀ : 0 < c₀)
    (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hδc : 2 * (C₀ + 5) * δ ≤ c₀)
    (k : ℕ) :
    ∀ p : ℕ, Even p → 2 ≤ p → ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Db DG : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (m : ℕ), WigSetting τ N A S → 1 ≤ m →
      PsiSmallW c₀ (specOf A) S →
      PropAW N (momMaxW C) allModelsW A S C₀ δ (m - 1) (δ / 8) Db →
      AnisotropicLawWAt N δ DG A (goeW N) S →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (W : Ω → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W →
        ∀ z ∈ levelSet N δ S m, ∀ v : Fin N → ℝ, testNorm v = 1 →
          ∫ ω, FvW A (W ω) z v ^ p ≤
            Kc * (((N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z) ^ p +
              ((N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ (PsiW (specOf A) z) k) ^ p) := by
  induction k with
  | zero =>
    intro p hp hp2
    obtain ⟨Kc, hKc, Ns, hs⟩ := cmp_stepB τ c₀ C p C₀ δ hτ hτ1 hc₀ hp hp2 hδ hC₀ hC₀δ hδc
    obtain ⟨Nr, hr⟩ := wig_rough_bound τ (momMaxW C) C₀ δ (δ / 8) (dPrev p + 1) hτ hτ1 hδ hC₀
      hC₀δ (by positivity)
    refine ⟨Kc, hKc, dPrev p + 1, 2 * p + 2, max (max Ns Nr) 1, ?_⟩
    intro N hN A S m hset hm hPs hPA hG Ω _ _ W hW z hz v hv
    have hN1 : 1 ≤ N := by omega
    have hNs : Ns ≤ N := by omega
    have hNr : Nr ≤ N := by omega
    have hPA' : PropAW N (momMaxW C) allModelsW A S C₀ δ (m - 1) (δ / 4) (dPrev p) :=
      cmp_propA_mono hset hN1 (by linarith) (by linarith) hPA
    have hB : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
        (W' : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W' →
        ∀ z ∈ levelSet N δ S m, ∀ v w : Fin N → ℝ, DomAt N (δ / 4) (dPrev p)
          (fun ω => ‖testBilin v (GW A (W' ω) z - piW A z) w‖)
          (fun _ => (N : ℝ) ^ (2 * δ) * (fun _ : ℂ => (1 : ℝ)) z * testNorm v * testNorm w) := by
      intro Ω' _ _ W' hW' z' hz' v' w'
      have h := (hr N hNr A S allModelsW m hset hm hPA Ω' W' hW' trivial z' hz').1 v' w'
      have e1 : 2 * (δ / 8) = δ / 4 := by ring
      have e2 : dPrev p + 1 - 1 = dPrev p := by ring
      rw [e1, e2] at h
      simpa only [mul_one] using h
    have h1 : ∀ z ∈ levelSet N δ S m, 0 ≤ (fun _ : ℂ => (1 : ℝ)) z ∧
        (fun _ : ℂ => (1 : ℝ)) z ≤ 1 + τ⁻¹ := fun _ _ =>
      ⟨zero_le_one, by have := inv_pos.2 hτ; simp only; linarith⟩
    have := hs N hNs A S m hset hm hPs hPA' hG (fun _ => 1) h1 hB Ω W hW z hz v hv
    simpa only [cmpPhi] using this
  | succ k ih =>
    intro p hp hp2
    set p' : ℕ := 2 * ⌈8 * (dPrev p + 1) / δ⌉₊ + 2 with hp'
    have hp'E : Even p' := ⟨⌈8 * (dPrev p + 1) / δ⌉₊ + 1, by omega⟩
    have hp'2 : 2 ≤ p' := by omega
    have hd0 : 0 ≤ dPrev p := by unfold dPrev; positivity
    have hp'D : dPrev p + 1 ≤ (δ / 4 - δ / 8) * p' := by
      have hc : 8 * (dPrev p + 1) / δ ≤ (⌈8 * (dPrev p + 1) / δ⌉₊ : ℝ) := Nat.le_ceil _
      have hpc : (p' : ℝ) = 2 * (⌈8 * (dPrev p + 1) / δ⌉₊ : ℝ) + 2 := by
        rw [hp']; push_cast; ring
      have h8 : 8 * (dPrev p + 1) = (8 * (dPrev p + 1) / δ) * δ := by field_simp
      rw [hpc]
      nlinarith
    obtain ⟨Kc', hKc', Db', DG', N', h'⟩ := ih p' hp'E hp'2
    obtain ⟨Kc, hKc, Ns, hs⟩ := cmp_stepB τ c₀ C p C₀ δ hτ hτ1 hc₀ hp hp2 hδ hC₀ hC₀δ hδc
    refine ⟨Kc, hKc, max Db' (dPrev p), max DG' (2 * p + 2),
      max (max (max N' Ns) 2) (max ⌈Kc' ^ (δ / 8)⁻¹⌉₊ ⌈(2 * ((k + 1 : ℕ) : ℝ)) ^ (τ / 4)⁻¹⌉₊), ?_⟩
    intro N hN A S m hset hm hPs hPA hG Ω _ _ W hW z hz v hv
    have hN' : N' ≤ N := by omega
    have hNs : Ns ≤ N := by omega
    have hN2 : 2 ≤ N := by omega
    have hN1 : 1 ≤ N := by omega
    have hNK : ⌈Kc' ^ (δ / 8)⁻¹⌉₊ ≤ N := by omega
    have hNk : ⌈(2 * ((k + 1 : ℕ) : ℝ)) ^ (τ / 4)⁻¹⌉₊ ≤ N := by omega
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNp : (0 : ℝ) < N := by linarith
    have hK' : Kc' ≤ (N : ℝ) ^ (δ / 8) := cmp_le_rpow' hKc' (by positivity) hNK
    have hk : 2 * ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (τ / 4) :=
      cmp_le_rpow' (by positivity) (by positivity) hNk
    have hPA1 : PropAW N (momMaxW C) allModelsW A S C₀ δ (m - 1) (δ / 8) Db' :=
      cmp_propA_mono hset hN1 le_rfl (le_max_left _ _) hPA
    have hPA2 : PropAW N (momMaxW C) allModelsW A S C₀ δ (m - 1) (δ / 4) (dPrev p) :=
      cmp_propA_mono hset hN1 (by linarith) (le_max_right _ _) hPA
    have hG1 := cmp_aniso_mono hN1 (le_max_left _ _) hG
    have hG2 := cmp_aniso_mono hN1 (le_max_right _ _) hG
    set Φf : ℂ → ℝ := fun z => cmpPhi N C₀ δ c₀ (PsiW (specOf A) z) (k + 1) with hΦf
    have hΦ : ∀ z ∈ levelSet N δ S m, 0 ≤ Φf z ∧ Φf z ≤ 1 + τ⁻¹ := fun z hz =>
      ⟨cmp_phi_nonneg (cmp_psi_pos hN1 _ (hset.domain.1 hz.1).1).le _,
        cmp_phi_le_one hN1 hτ hτ1 hδ hc₀.le hC₀δ _ (hset.domain.1 hz.1) (k + 1) hk⟩
    have hB : ∀ (Ω' : Type) [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
        (W' : Ω' → Matrix (Fin N) (Fin N) ℝ), WigClassEntries (momMaxW C) N W' →
        ∀ z ∈ levelSet N δ S m, ∀ v w : Fin N → ℝ, DomAt N (δ / 4) (dPrev p)
          (fun ω => ‖testBilin v (GW A (W' ω) z - piW A z) w‖)
          (fun _ => (N : ℝ) ^ (2 * δ) * Φf z * testNorm v * testNorm w) := by
      intro Ω' _ _ W' hW' z' hz' v' w'
      have hz'D := hset.domain.1 hz'.1
      have hΨ' := cmp_psi_pos hN1 (specOf A) hz'D.1
      set a : ℝ := (N : ℝ) ^ (C₀ * δ) * PsiW (specOf A) z' with ha
      set b : ℝ := (N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ (PsiW (specOf A) z') k with hb
      have ha0 : 0 < a := mul_pos (Real.rpow_pos_of_pos hNp _) hΨ'
      have hb0 : 0 ≤ b := mul_nonneg (Real.rpow_nonneg hNp.le _) (cmp_phi_nonneg hΨ'.le _)
      have hY : (N : ℝ) ^ (2 * δ) * Φf z' = a + b := by
        simp only [hΦf, ha, hb]
        exact cmp_phi_succ_mul hN1 C₀ δ c₀ _ k
      have hYpos : 0 < (N : ℝ) ^ (2 * δ) * Φf z' := by rw [hY]; linarith
      refine cmp_bilin_of_diag (B := fun ω => GW A (W' ω) z' - piW A z')
        (fun ω => cmp_GW_sub_piW_symm hset.symmA (hW'.symm ω) z') hN2
        (fun u hu => ?_) v' w'
      have hmom : ∫ ω, FvW A (W' ω) z' u ^ p' ≤ Kc' * (a ^ p' + b ^ p') :=
        h' N hN' A S m hset hm hPs hPA1 hG1 Ω' W' hW' z' hz' u hu
      refine DomAt.of_moment (ε := δ / 8) p' hN1 hp'D (fun ω => norm_nonneg _) hYpos
        (cmp_integrable_Fv_pow hset hW' hz'.1 hu p') (hmom.trans ?_)
      rw [hY]
      have hsum : a ^ p' + b ^ p' ≤ (a + b) ^ p' := pow_add_pow_le ha0.le hb0 (by omega)
      have hNp' : (N : ℝ) ^ (δ / 8) ≤ ((N : ℝ) ^ (δ / 8)) ^ p' :=
        le_self_pow₀ (Real.one_le_rpow hN1r (by positivity)) (by omega)
      calc Kc' * (a ^ p' + b ^ p') ≤ (N : ℝ) ^ (δ / 8) * (a + b) ^ p' :=
            mul_le_mul hK' hsum (by positivity) (Real.rpow_nonneg hNp.le _)
        _ ≤ ((N : ℝ) ^ (δ / 8)) ^ p' * (a + b) ^ p' :=
            mul_le_mul_of_nonneg_right hNp' (by positivity)
        _ = ((N : ℝ) ^ (δ / 8) * (a + b)) ^ p' := by rw [mul_pow]
    exact hs N hNs A S m hset hm hPs hPA2 hG2 Φf hΦ hB Ω W hW z hz v hv

/-- The induction step for the whole class (case (b)): (A_{m−1}) for the whole class at
`(δ/8, D_b)` and the Gaussian start give (C_m) for the whole class at `(δ/8, D)`. -/
private lemma cmp_stepC (τ c₀ : ℝ) (C : ℕ → ℝ) (C₀ δ D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4)
    (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    ∃ Db DG : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (m : ℕ),
      WigSetting τ N A S → 1 ≤ m → PsiSmallW c₀ (specOf A) S →
      PropAW N (momMaxW C) allModelsW A S C₀ δ (m - 1) (δ / 8) Db →
      AnisotropicLawWAt N δ DG A (goeW N) S →
      PropCW N (momMaxW C) allModelsW A S C₀ δ m (δ / 8) D := by
  set K : ℕ := ⌈2 / c₀⌉₊ + 1 with hKdef
  set p := markovPow δ D with hpdef
  have hpE : Even p := cmp_markovPow_even δ D
  have hp2 : 2 ≤ p := cmp_markovPow_two δ D
  obtain ⟨Kc, hKc, Db, DG, N', h'⟩ := cmp_iter τ c₀ C C₀ δ hτ hτ1 hc₀ hδ hC₀ hC₀δ hδc K p hpE hp2
  set Kp : ℝ := Kc * (1 + ((K : ℝ) + 1) ^ p) with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  refine ⟨Db, DG, max (max N' ⌈Kp ^ (δ / 16)⁻¹⌉₊) (max 1 ⌈τ⁻¹ ^ (c₀ / 2)⁻¹⌉₊), ?_⟩
  intro N hN A S m hset hm hPs hPA hG
  have hN' : N' ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNK : ⌈Kp ^ (δ / 16)⁻¹⌉₊ ≤ N := by omega
  have hNc : ⌈τ⁻¹ ^ (c₀ / 2)⁻¹⌉₊ ≤ N := by omega
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hτc : τ⁻¹ ≤ (N : ℝ) ^ (c₀ / 2) :=
    cmp_le_rpow' (inv_pos.2 hτ).le (by positivity) hNc
  refine cmp_propC_of_moment (ε := δ / 16) (Kp := Kp) hset hN1 (cmp_markovPow_ge hδ D) ?_ ?_
  · have hK := cmp_le_rpow' hKp0 (by positivity : (0 : ℝ) < δ / 16) hNK
    refine hK.trans (Real.rpow_le_rpow_of_exponent_le hN1r ?_)
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    nlinarith
  · intro Ω _ _ W hW _ z hz v hv
    have hmom := h' N hN' A S m hset hm hPs hPA hG Ω W hW z hz v hv
    have hzD := hset.domain.1 hz.1
    set Ψ := PsiW (specOf A) z with hΨdef
    have hΨ0 : 0 < Ψ := cmp_psi_pos hN1 _ hzD.1
    have hΨτ : τ / N ≤ Ψ := cmp_psi_ge hN1 hτ _ hzD
    set a : ℝ := (N : ℝ) ^ (C₀ * δ) * Ψ with ha
    have hC0 : 0 ≤ C₀ * δ := by nlinarith
    have hNa : 1 ≤ (N : ℝ) ^ (C₀ * δ) := Real.one_le_rpow hN1r hC0
    have hΨa : Ψ ≤ a := le_mul_of_one_le_left hΨ0.le hNa
    have ha0 : 0 ≤ a := le_trans hΨ0.le hΨa
    -- `N^{−c₀/2} Φ_K ≤ (K + 1) a`
    have hφ := cmp_phi_le hN1 (C₀ := C₀) hδ.le hc₀.le hΨ0.le K
    have hy : (N : ℝ) ^ ((C₀ - 2) * δ) * Ψ ≤ a :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)) hΨ0.le
    have hr1 : (N : ℝ) ^ (-c₀ / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
    have hr0 : 0 ≤ (N : ℝ) ^ (-c₀ / 2) := Real.rpow_nonneg hNp.le _
    have hK2 : 2 / c₀ ≤ (K : ℝ) := by
      rw [hKdef]; push_cast
      linarith [Nat.le_ceil (2 / c₀)]
    have htail : (N : ℝ) ^ (-c₀ / 2) * (N : ℝ) ^ (-((K : ℝ) * c₀ / 2)) ≤ a := by
      rw [← Real.rpow_add hNp]
      have hexp : -c₀ / 2 + -((K : ℝ) * c₀ / 2) ≤ -1 + -(c₀ / 2) := by
        have : 2 ≤ (K : ℝ) * c₀ := by
          have := mul_le_mul_of_nonneg_right hK2 hc₀.le
          rwa [div_mul_cancel₀ _ hc₀.ne'] at this
        linarith
      calc (N : ℝ) ^ (-c₀ / 2 + -((K : ℝ) * c₀ / 2)) ≤ (N : ℝ) ^ (-1 + -(c₀ / 2)) :=
            Real.rpow_le_rpow_of_exponent_le hN1r hexp
        _ = (N : ℝ)⁻¹ * ((N : ℝ) ^ (c₀ / 2))⁻¹ := by
            rw [Real.rpow_add hNp, Real.rpow_neg_one, Real.rpow_neg hNp.le]
        _ ≤ (N : ℝ)⁻¹ * τ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hpos : 0 < (N : ℝ) ^ (c₀ / 2) := Real.rpow_pos_of_pos hNp _
            rw [inv_le_comm₀ hpos hτ]
            exact hτc
        _ = τ / N := by ring
        _ ≤ a := hΨτ.trans hΨa
    have hbound : (N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ Ψ K ≤ ((K : ℝ) + 1) * a := by
      have hφ0 := cmp_phi_nonneg (N := N) (C₀ := C₀) (δ := δ) (c₀ := c₀) hΨ0.le K
      calc (N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ Ψ K
          ≤ (N : ℝ) ^ (-c₀ / 2) * ((K : ℝ) * ((N : ℝ) ^ ((C₀ - 2) * δ) * Ψ) +
              (N : ℝ) ^ (-((K : ℝ) * c₀ / 2))) := mul_le_mul_of_nonneg_left hφ hr0
        _ = (N : ℝ) ^ (-c₀ / 2) * ((K : ℝ) * ((N : ℝ) ^ ((C₀ - 2) * δ) * Ψ)) +
              (N : ℝ) ^ (-c₀ / 2) * (N : ℝ) ^ (-((K : ℝ) * c₀ / 2)) := by ring
        _ ≤ (K : ℝ) * a + a := by
            have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
            have h1 : (N : ℝ) ^ (-c₀ / 2) * ((K : ℝ) * ((N : ℝ) ^ ((C₀ - 2) * δ) * Ψ)) ≤
                (K : ℝ) * a := by
              have hy0 : 0 ≤ (N : ℝ) ^ ((C₀ - 2) * δ) * Ψ :=
                mul_nonneg (Real.rpow_nonneg hNp.le _) hΨ0.le
              calc (N : ℝ) ^ (-c₀ / 2) * ((K : ℝ) * ((N : ℝ) ^ ((C₀ - 2) * δ) * Ψ))
                  ≤ 1 * ((K : ℝ) * ((N : ℝ) ^ ((C₀ - 2) * δ) * Ψ)) :=
                    mul_le_mul_of_nonneg_right hr1 (mul_nonneg hk0 hy0)
                _ ≤ (K : ℝ) * a := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hy hk0
            linarith
        _ = ((K : ℝ) + 1) * a := by ring
    have hb0 : 0 ≤ (N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ Ψ K :=
      mul_nonneg hr0 (cmp_phi_nonneg hΨ0.le K)
    have hbp : ((N : ℝ) ^ (-c₀ / 2) * cmpPhi N C₀ δ c₀ Ψ K) ^ p ≤ ((K : ℝ) + 1) ^ p * a ^ p := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hb0 hbound p
    calc ∫ ω, FvW A (W ω) z v ^ p ≤ Kc * (a ^ p + ((N : ℝ) ^ (-c₀ / 2) *
          cmpPhi N C₀ δ c₀ Ψ K) ^ p) := hmom
      _ ≤ Kc * (a ^ p + ((K : ℝ) + 1) ^ p * a ^ p) := by gcongr
      _ = Kp * a ^ p := by rw [hKp]; ring

/-- (A_l) for the whole class at every level `l ≤ L`, from (A_0) and the induction step. -/
private lemma cmp_levels (τ c₀ : ℝ) (C : ℕ → ℝ) (C₀ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hc₀ : 0 < c₀)
    (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hδc : 2 * (C₀ + 5) * δ ≤ c₀)
    (L : ℕ) : ∀ D : ℝ, ∃ DG : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ)
      (S : Set ℂ), WigSetting τ N A S → PsiSmallW c₀ (specOf A) S →
      AnisotropicLawWAt N δ DG A (goeW N) S →
      ∀ l ≤ L, PropAW N (momMaxW C) allModelsW A S C₀ δ l (δ / 8) D := by
  induction L with
  | zero =>
    intro D
    obtain ⟨N₀, h₀⟩ := wig_propA_zero τ (momMaxW C) (δ / 8) D hτ hτ1 (by positivity)
    refine ⟨0, N₀, fun N hN A S hset _ _ l hl => ?_⟩
    obtain rfl : l = 0 := by omega
    exact h₀ N hN A S allModelsW C₀ δ hset (by linarith) hδ.le
  | succ L ih =>
    intro D
    obtain ⟨Db, DGc, Nc, hc⟩ := cmp_stepC τ c₀ C C₀ δ D hτ hτ1 hc₀ hδ hC₀ hC₀δ hδc
    obtain ⟨DG', N', h'⟩ := ih (max D Db)
    set Kτ : ℝ := τ⁻¹ ^ 2 * (1 + (3 * τ⁻¹ + 1) ^ 2) with hKτ
    have hKτ0 : 0 ≤ Kτ := by positivity
    refine ⟨max DG' DGc, max (max N' Nc) (max 1 ⌈Kτ ^ (δ / 8)⁻¹⌉₊), ?_⟩
    intro N hN A S hset hPs hG l hl
    have hN' : N' ≤ N := by omega
    have hNc : Nc ≤ N := by omega
    have hN1 : 1 ≤ N := by omega
    have hNK : ⌈Kτ ^ (δ / 8)⁻¹⌉₊ ≤ N := by omega
    have hG' := cmp_aniso_mono hN1 (le_max_left _ _) hG
    have hGc := cmp_aniso_mono hN1 (le_max_right _ _) hG
    have hall := h' N hN' A S hset hPs hG'
    rcases Nat.lt_or_ge l (L + 1) with hlt | hge
    · exact cmp_propA_mono hset hN1 le_rfl (le_max_left _ _) (hall l (by omega))
    · obtain rfl : l = L + 1 := by omega
      have hA : PropAW N (momMaxW C) allModelsW A S C₀ δ (L + 1 - 1) (δ / 8) Db := by
        rw [show L + 1 - 1 = L by omega]
        exact cmp_propA_mono hset hN1 le_rfl (le_max_right _ _) (hall L le_rfl)
      have hC := hc N hNc A S (L + 1) hset (by omega) hPs hA hGc
      exact cmp_propA_of_propC hset hN1 (cmp_le_rpow' hKτ0 (by positivity) hNK) hC

/-- Case (b) of the induction step: under `Ψ ≤ N^{−1/4−c₀}`, the Gaussian start alone gives (C_m)
for every class `P`, through (C_m) for the whole class. -/
private lemma cmp_caseB (τ c₀ : ℝ) (C : ℕ → ℝ) (C₀ δ D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4)
    (hδc : 2 * (C₀ + 5) * δ ≤ c₀) :
    ∃ DG : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (m : ℕ)
      (P : ModelClassW N), WigSetting τ N A S → 1 ≤ m → PsiSmallW c₀ (specOf A) S →
      AnisotropicLawWAt N δ DG A (goeW N) S →
      PropCW N (momMaxW C) P A S C₀ δ m (δ / 8) D := by
  obtain ⟨Db, DGc, Nc, hc⟩ := cmp_stepC τ c₀ C C₀ δ D hτ hτ1 hc₀ hδ hC₀ hC₀δ hδc
  obtain ⟨DGl, Nl, hl⟩ := cmp_levels τ c₀ C C₀ δ hτ hτ1 hc₀ hδ hC₀ hC₀δ hδc (topLevel τ δ) Db
  refine ⟨max DGc DGl, max (max Nc Nl) 1, ?_⟩
  intro N hN A S m P hset hm hPs hG
  have hNc : Nc ≤ N := by omega
  have hNl : Nl ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hGc := cmp_aniso_mono hN1 (le_max_left _ _) hG
  have hGl := cmp_aniso_mono hN1 (le_max_right _ _) hG
  set m' := min m (topLevel τ δ) with hm'
  have hm'1 : 1 ≤ m' := le_min hm (le_max_left _ _)
  have hm'L : m' - 1 ≤ topLevel τ δ := by omega
  have hA := hl N hNl A S hset hPs hGl (m' - 1) hm'L
  have hC := hc N hNc A S m' hset hm'1 hPs hA hGc
  have hlev := cmp_levelSet_min hN1 hδ hset.domain.1 m
  intro Ω _ _ W hW _ z hz v hv
  rw [hlev] at hz
  exact hC Ω W hW trivial z hz v hv

/-- Lemma 7.4 analogue (the induction step, the `Φ`-iteration included): (A_{m−1}) for the
class gives (C_m) for the class. -/
theorem wig_propC_of_propA (τ c₀ : ℝ) (C : ℕ → ℝ) (C₀ δ D : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hC₀ : 30 ≤ C₀) (hC₀δ : C₀ * δ ≤ τ / 4) (hδc : 2 * (C₀ + 5) * δ ≤ c₀)
    (hD : 0 ≤ D) :
    ∃ DG DA : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : Matrix (Fin N) (Fin N) ℝ) (S : Set ℂ) (m : ℕ)
      (P : ModelClassW N), WigSetting τ N A S → 1 ≤ m →
      (P = zeroThirdW ∨ PsiSmallW c₀ (specOf A) S) →
      AnisotropicLawWAt N δ DG A (goeW N) S →
      PropAW N (momMaxW C) P A S C₀ δ (m - 1) (δ / 4) DA →
      PropCW N (momMaxW C) P A S C₀ δ m (δ / 8) D := by
  have _hD := hD
  obtain ⟨Na, ha⟩ := cmp_caseA τ C C₀ δ D hτ hτ1 hδ hC₀ hC₀δ
  obtain ⟨DGb, Nb, hb⟩ := cmp_caseB τ c₀ C C₀ δ D hτ hτ1 hc₀ hδ hC₀ hC₀δ hδc
  refine ⟨max DGb (2 * markovPow δ D + 2), dPrev (markovPow δ D), max (max Na Nb) 1, ?_⟩
  intro N hN A S m P hset hm hP hG hA
  have hN1 : 1 ≤ N := by omega
  rcases hP with rfl | hPs
  · exact ha N (by omega) A S m hset hm (cmp_aniso_mono hN1 (le_max_right _ _) hG) hA
  · exact hb N (by omega) A S m P hset hm hPs (cmp_aniso_mono hN1 (le_max_left _ _) hG)

#print axioms Anisotropic.wig_propC_of_propA

end Anisotropic
