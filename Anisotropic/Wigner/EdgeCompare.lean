import Anisotropic.Comparison.Interpolation
import Anisotropic.EdgeUniv.Reduction
import Anisotropic.EdgeUniv.SmCount
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.EdgeDefs
import Anisotropic.Wigner.EdgeSwap
import Anisotropic.Wigner.Interp
import Anisotropic.Wigner.Model
import Anisotropic.Wigner.EdgeSym

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The third-order sum and the comparison of smooth functionals of the smoothed counts for `W + A` -/

/-! ## The resolvent of a real symmetric matrix -/

section Resolvent

variable {N : ℕ}


private lemma ecw_symm_of_herm {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  have h := hA.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at h

private lemma ecw_herm_of_symm {A : Matrix (Fin N) (Fin N) ℝ} (hA : Aᵀ = A) : A.IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- A real symmetric `H = U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma ecw_eig_decomp {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      H = U * diagonal (specOf H) * Uᵀ := by
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at h
  · have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [specOf_eq hH]
    simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

private lemma ecw_cplx_orth {U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1) :
    cplx U * (cplx U)ᵀ = 1 := by
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
  simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_map] at h ⊢
  exact h

/-- `(H − z)` times the rotated diagonal `(λₖ − z)⁻¹` is the identity. -/
private lemma ecw_right_inv {H U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1)
    (hUU' : Uᵀ * U = 1) (hHU : H = U * diagonal (specOf H) * Uᵀ) {z : ℂ} (hz : 0 < z.im) :
    (cplx H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      (cplx U * diagonal (fun k => ((specOf H k : ℂ) - z)⁻¹) * (cplx U)ᵀ) = 1 := by
  have hP := ecw_cplx_orth hUU
  have hP' := ecw_cplx_orth (U := Uᵀ) (by rw [Matrix.transpose_transpose]; exact hUU')
  simp only [cplx, Matrix.transpose_map, Matrix.transpose_transpose] at hP'
  have hne : ∀ k, (specOf H k : ℂ) - z ≠ 0 := fun k h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hM : cplx H - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * diagonal (fun k => (specOf H k : ℂ) - z) * (cplx U)ᵀ := by
    have h1 : cplx H = cplx U * diagonal (fun k => (specOf H k : ℂ)) * (cplx U)ᵀ := by
      conv_lhs => rw [hHU]
      simp only [cplx, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
      simp
    have h2 : diagonal (fun k => (specOf H k : ℂ) - z) =
        diagonal (fun k => (specOf H k : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab]
    rw [h2, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP]
  rw [hM]
  calc cplx U * diagonal (fun k => (specOf H k : ℂ) - z) * (cplx U)ᵀ *
        (cplx U * diagonal (fun k => ((specOf H k : ℂ) - z)⁻¹) * (cplx U)ᵀ)
      = cplx U * diagonal (fun k => (specOf H k : ℂ) - z) * ((cplx U)ᵀ * cplx U) *
        diagonal (fun k => ((specOf H k : ℂ) - z)⁻¹) * (cplx U)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        simp only [cplx] at hP' ⊢
        rw [hP', Matrix.mul_one, Matrix.mul_assoc (U.map (algebraMap ℝ ℂ)),
          Matrix.diagonal_mul_diagonal]
        have : (fun k => ((specOf H k : ℂ) - z) * ((specOf H k : ℂ) - z)⁻¹) = fun _ => 1 := by
          funext k
          exact mul_inv_cancel₀ (hne k)
        rw [this, Matrix.diagonal_one, Matrix.mul_one]
        exact hP

/-- The spectral form `G^W(z) = U diag((λₖ − z)⁻¹) Uᵀ` of the resolvent of the symmetric
`W + A`. -/
private lemma ecw_GW_eq {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * GW A Wm z = 1 ∧
      GW A Wm z = cplx U * diagonal (fun k => ((specOf (Wm + A) k : ℂ) - z)⁻¹) * (cplx U)ᵀ := by
  obtain ⟨U, hUU, hUU', hHU⟩ := ecw_eig_decomp hH
  have hR := ecw_right_inv hUU hUU' hHU hz
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((specOf (Wm + A) k : ℂ) - z)⁻¹) *
      (cplx U)ᵀ := Matrix.inv_eq_right_inv hR
  exact ⟨U, hUU, by rw [hG]; exact hR, hG⟩

private lemma ecw_mul_GW {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * GW A Wm z = 1 :=
  (ecw_GW_eq hH hz).choose_spec.2.1

private lemma ecw_GW_mul {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    GW A Wm z * (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 :=
  mul_eq_one_comm.1 (ecw_mul_GW hH hz)

private lemma ecw_isUnit {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
  Matrix.isUnit_det_of_right_inverse (ecw_mul_GW hH hz)

/-- `G^W` is symmetric. -/
private lemma ecw_GW_transpose {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : (GW A Wm z)ᵀ = GW A Wm z := by
  obtain ⟨U, -, -, hG⟩ := ecw_GW_eq hH hz
  rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- `tr G^W(z) = ∑ₖ (λₖ − z)⁻¹`. -/
private lemma ecw_trace_GW {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    trace (GW A Wm z) = ∑ k, ((specOf (Wm + A) k : ℂ) - z)⁻¹ := by
  obtain ⟨U, hUU, -, hG⟩ := ecw_GW_eq hH hz
  have hP := ecw_cplx_orth hUU
  have hP' : (cplx U)ᵀ * cplx U = 1 := mul_eq_one_comm.1 hP
  rw [hG, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.trace_diagonal]

/-- `|(λ − z)⁻¹| ≤ (Im z)⁻¹`. -/
private lemma ecw_norm_inv_le (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  have h1 : z.im ≤ ‖(x : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
    exact this
  have h2 : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le hz h1
  rw [norm_inv, one_div]
  exact inv_anti₀ hz h1

/-- The entries of `G^W(z)` are at most `(Im z)⁻¹` in modulus. -/
private lemma ecw_GW_entry_le {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (s t : Fin N) : ‖GW A Wm z s t‖ ≤ 1 / z.im := by
  obtain ⟨U, hUU, -, hG⟩ := ecw_GW_eq hH hz
  have hrow : ∀ s, ∑ k, U s k ^ 2 = 1 := fun s => by
    have := congrFun (congrFun hUU s) s
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by ring
  have he : GW A Wm z s t = ∑ k, (U s k : ℂ) * ((specOf (Wm + A) k : ℂ) - z)⁻¹ * (U t k : ℂ) := by
    rw [hG, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · simp [cplx]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · simp
  rw [he]
  have hz0 : 0 ≤ 1 / z.im := by positivity
  calc ‖∑ k, (U s k : ℂ) * ((specOf (Wm + A) k : ℂ) - z)⁻¹ * (U t k : ℂ)‖
      ≤ ∑ k, ‖(U s k : ℂ) * ((specOf (Wm + A) k : ℂ) - z)⁻¹ * (U t k : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k, 1 / z.im * ((U s k ^ 2 + U t k ^ 2) / 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        have h1 := ecw_norm_inv_le (specOf (Wm + A) k) hz
        have h2 : |U s k| * |U t k| ≤ (U s k ^ 2 + U t k ^ 2) / 2 := by
          nlinarith [sq_nonneg (|U s k| - |U t k|), sq_abs (U s k), sq_abs (U t k)]
        calc |U s k| * ‖((specOf (Wm + A) k : ℂ) - z)⁻¹‖ * |U t k|
            = ‖((specOf (Wm + A) k : ℂ) - z)⁻¹‖ * (|U s k| * |U t k|) := by ring
          _ ≤ 1 / z.im * ((U s k ^ 2 + U t k ^ 2) / 2) :=
              mul_le_mul h1 h2 (by positivity) hz0
    _ = 1 / z.im := by
        rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hrow, hrow]
        ring

/-- The second resolvent identity `G' − G = G' (H − H') G`. -/
private lemma ecw_res_sub {A Wm Wm' : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    (hH' : (Wm' + A).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    GW A Wm' z - GW A Wm z = GW A Wm' z * (cplx (Wm + A) - cplx (Wm' + A)) * GW A Wm z := by
  have e : cplx (Wm + A) - cplx (Wm' + A) =
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) -
        (cplx (Wm' + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) := by abel
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, ecw_mul_GW hH hz, Matrix.mul_one,
    ecw_GW_mul hH' hz, Matrix.one_mul]

/-- `p ↦ G^W(p)` is continuous along a continuous family of symmetric matrices and spectral
parameters in the upper half-plane. -/
private lemma ecw_continuous_GW {X : Type*} [TopologicalSpace X] (A : Matrix (Fin N) (Fin N) ℝ)
    {Wf : X → Matrix (Fin N) (Fin N) ℝ} {zf : X → ℂ} (hWf : Continuous Wf) (hzf : Continuous zf)
    (hH : ∀ p, (Wf p + A).IsHermitian) (hz : ∀ p, 0 < (zf p).im) :
    Continuous fun p => GW A (Wf p) (zf p) := by
  have hM : Continuous fun p => cplx (Wf p + A) - zf p • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    have h1 : Continuous fun p => cplx (Wf p + A) :=
      ((hWf.add continuous_const).matrix_map Complex.continuous_ofReal)
    exact h1.sub (hzf.smul continuous_const)
  rw [continuous_iff_continuousAt]
  intro p
  have hu := ecw_isUnit (hH p) (hz p)
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  exact hinv.comp (f := fun p => cplx (Wf p + A) - zf p • (1 : Matrix (Fin N) (Fin N) ℂ))
    hM.continuousAt


end Resolvent

/-! ## Updates of a symmetric entry -/

section Update

variable {N : ℕ}


private lemma ecw_Wupd_symm {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm) (i j : Fin N)
    (t : ℝ) : (Wupd Wm i j t)ᵀ = Wupd Wm i j t := by
  ext s u
  simp only [Matrix.transpose_apply, Wupd]
  by_cases h : (s = i ∧ u = j) ∨ (s = j ∧ u = i)
  · have h' : (u = i ∧ s = j) ∨ (u = j ∧ s = i) := by tauto
    simp only [h, h', ite_true]
  · have h' : ¬((u = i ∧ s = j) ∨ (u = j ∧ s = i)) := by tauto
    simp only [h, h', ite_false]
    have := congrFun (congrFun hW s) u
    simpa [Matrix.transpose_apply] using this

private lemma ecw_Wupd_herm {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) (i j : Fin N) (t : ℝ) : (Wupd Wm i j t + A).IsHermitian :=
  (ecw_herm_of_symm (ecw_Wupd_symm (ecw_symm_of_herm hW) i j t)).add hA

private lemma ecw_Wupd_self {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm) (i j : Fin N) :
    Wupd Wm i j (Wm i j) = Wm := by
  funext a b
  by_cases h : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
  · simp only [Wupd, h, ite_true]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · have := congrFun (congrFun hW a) b
      simpa [Matrix.transpose_apply] using this
  · simp [Wupd, h]

/-- `H(t) − H(x) = (t − x) Δ` along the entry `(i, j)`. -/
private lemma ecw_cplx_Wupd_sub (A Wm : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (t x : ℝ) :
    cplx (Wupd Wm i j t + A) - cplx (Wupd Wm i j x + A) = ((t - x : ℝ) : ℂ) • deltaW i j := by
  ext a b
  simp only [cplx, Matrix.sub_apply, Matrix.map_apply, Matrix.add_apply, Wupd, deltaW,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma ecw_continuous_Wupd (i j : Fin N) :
    Continuous fun p : Matrix (Fin N) (Fin N) ℝ × ℝ => Wupd p.1 i j p.2 := by
  refine continuous_matrix fun a b => ?_
  by_cases h : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
  · simpa [Wupd, h] using continuous_snd
  · have hc : Continuous fun p : Matrix (Fin N) (Fin N) ℝ × ℝ => p.1 a b :=
      (continuous_id.matrix_elem a b).comp continuous_fst
    simpa [Wupd, h] using hc


end Update

/-! ## The smoothed count as an integral of `Im tr G^W` and its entry derivatives -/

section Derivative

variable {N : ℕ}


/-- The imaginary part of one pole term. -/
private lemma ecw_im_pole (lam y η : ℝ) :
    (((lam : ℂ) - (y + η * Complex.I))⁻¹).im = η / ((lam - y) ^ 2 + η ^ 2) := by
  rw [Complex.inv_im]
  have h1 : ((lam : ℂ) - (y + η * Complex.I)).im = -η := by simp
  rw [h1, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, zero_sub]
  rw [neg_neg]
  congr 1; ring

/-- `∫_{E₁}^{E₂} η / ((λ - y)² + η²) dy = arctan((E₂ - λ)/η) - arctan((E₁ - λ)/η)`. -/
private lemma ecw_integral_pole (lam η E₁ E₂ : ℝ) (hη : 0 < η) :
    ∫ y in E₁..E₂, η / ((lam - y) ^ 2 + η ^ 2) =
      Real.arctan ((E₂ - lam) / η) - Real.arctan ((E₁ - lam) / η) := by
  have hd : ∀ y ∈ Set.uIcc E₁ E₂,
      HasDerivAt (fun y : ℝ => Real.arctan ((y - lam) / η)) (η / ((lam - y) ^ 2 + η ^ 2)) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => (y - lam) / η) (1 / η) y :=
      ((hasDerivAt_id y).sub_const lam).div_const η
    have h2 := h1.arctan
    convert h2 using 1
    field_simp
    ring
  have hc : Continuous fun y : ℝ => η / ((lam - y) ^ 2 + η ^ 2) := by
    refine continuous_const.div (by fun_prop) fun y => by positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)

/-- `𝒳_{[E₁,E₂]}(W + A) = π⁻¹ ∫_{E₁}^{E₂} Im tr G^W(y + iη) dy` for symmetric `W + A`. -/
private lemma ecw_smCount_eq {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    smCount (Wm + A) η E₁ E₂ =
      Real.pi⁻¹ * ∫ y in E₁..E₂, (trace (GW A Wm ((y : ℂ) + η * Complex.I))).im := by
  have hz : ∀ y : ℝ, 0 < ((y : ℂ) + η * Complex.I).im := fun y => by simpa using hη
  have him : ∀ y : ℝ, (trace (GW A Wm ((y : ℂ) + η * Complex.I))).im =
      ∑ k, η / ((specOf (Wm + A) k - y) ^ 2 + η ^ 2) := by
    intro y
    rw [ecw_trace_GW hH (hz y), Complex.im_sum]
    simp only [ecw_im_pole _ y η]
  simp only [him]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [ecw_integral_pole _ η E₁ E₂ hη]
    unfold smCount
    rw [← Finset.sum_div, div_eq_inv_mul]
  · intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.div (by fun_prop) fun y => by positivity

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def EcwMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private lemma ecw_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : EcwMD f f' x) (hg : EcwMD g g' x) :
    EcwMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private lemma ecw_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    EcwMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

private lemma ecw_MD_trace {ι : Type*} [Fintype ι] {f : ℝ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ}
    {x : ℝ} (hf : EcwMD f f' x) : HasDerivAt (fun y => trace (f y)) (trace f') x := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact HasDerivAt.fun_sum fun s _ => hf s s

private lemma ecw_hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The entrywise derivative from a difference identity `f(x + h) − f(x) = h • D(h)` with `D`
continuous at `0`. -/
private lemma ecw_MD_of_sub {ι : Type*} {f : ℝ → Matrix ι ι ℂ} {D : ℝ → Matrix ι ι ℂ} {x : ℝ}
    (hid : ∀ h : ℝ, f (x + h) - f x = (h : ℂ) • D h)
    (hc : ∀ s t, ContinuousAt (fun h => D h s t) 0) : EcwMD f (D 0) x := by
  intro s t
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim := (hc s t).tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (h : ℂ) ≠ 0 := by simpa using hh
  have := congrFun (congrFun (hid h) s) t
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this, Complex.real_smul]
  push_cast
  field_simp

/-- `y ↦ G^W(W^{y}_{(ij)}, z)` is continuous. -/
private lemma ecw_continuous_G_t {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    Continuous fun y => GW A (Wupd Wm i j y) z :=
  ecw_continuous_GW A ((ecw_continuous_Wupd i j).comp (continuous_const.prodMk continuous_id))
    continuous_const (fun y => ecw_Wupd_herm hA hW i j y) fun _ => hz

/-- `d/dt G^W(W^{t}_{(ij)}) = −G Δ G`. -/
private lemma ecw_MD_G {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) :
    EcwMD (fun y => GW A (Wupd Wm i j y) z)
      (-(GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j x) z)) x := by
  have hid : ∀ h : ℝ, GW A (Wupd Wm i j (x + h)) z - GW A (Wupd Wm i j x) z =
      (h : ℂ) • (-(GW A (Wupd Wm i j (x + h)) z * deltaW i j * GW A (Wupd Wm i j x) z)) := by
    intro h
    rw [ecw_res_sub (ecw_Wupd_herm hA hW i j x) (ecw_Wupd_herm hA hW i j (x + h)) hz,
      ecw_cplx_Wupd_sub, show x - (x + h) = -h by ring]
    simp
  have h := ecw_MD_of_sub (f := fun y => GW A (Wupd Wm i j y) z) (D := fun h =>
    -(GW A (Wupd Wm i j (x + h)) z * deltaW i j * GW A (Wupd Wm i j x) z)) hid ?_
  · simpa using h
  · intro s t
    have hc : Continuous fun h : ℝ => GW A (Wupd Wm i j (x + h)) z :=
      (ecw_continuous_G_t hA hW hz i j).comp (continuous_const.add continuous_id)
    have hc2 : Continuous fun h : ℝ =>
        -(GW A (Wupd Wm i j (x + h)) z * deltaW i j * GW A (Wupd Wm i j x) z) :=
      ((hc.matrix_mul continuous_const).matrix_mul continuous_const).neg
    exact ((continuous_apply_apply s t).comp hc2).continuousAt


end Derivative

/-! ## The higher entry derivatives -/

section Higher

variable {N : ℕ}


/-- `d/dt (Δ G)^k = -k (Δ G)^{k+1}`. -/
private lemma ecw_MD_pow {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    EcwMD (fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-(k : ℂ) • (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using ecw_MD_const (1 : Matrix (Fin N) (Fin N) ℂ) x
  | succ k ih =>
    have hDG := ecw_MD_mul (ecw_MD_const (deltaW i j) x) (ecw_MD_G hA hW hz i j x)
    have h := ecw_MD_mul ih hDG
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

/-- The coefficients `-π⁻¹ (-1)^k k! Im [tr (Δ G)^{k+1}]` between the endpoints. -/
private def ecwPsi (A Wm : Matrix (Fin N) (Fin N) ℝ) (η E₁ E₂ : ℝ) (i j : Fin N) (k : ℕ)
    (t : ℝ) : ℝ :=
  -(1 / Real.pi) * (((-1 : ℝ) ^ k * (k.factorial : ℝ)) *
    ((trace ((deltaW i j * GW A (Wupd Wm i j t) ((E₂ : ℂ) + η * Complex.I)) ^ (k + 1))).im -
      (trace ((deltaW i j * GW A (Wupd Wm i j t) ((E₁ : ℂ) + η * Complex.I)) ^ (k + 1))).im))

private lemma ecw_hasDerivAt_psi {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (k : ℕ) (x : ℝ) :
    HasDerivAt (ecwPsi A Wm η E₁ E₂ i j k) (ecwPsi A Wm η E₁ E₂ i j (k + 1) x) x := by
  have hb : 0 < ((E₂ : ℂ) + η * Complex.I).im := by simpa using hη
  have ha : 0 < ((E₁ : ℂ) + η * Complex.I).im := by simpa using hη
  have h2 := ecw_hasDerivAt_im (ecw_MD_trace (ecw_MD_pow hA hW hb i j x (k + 1)))
  have h1 := ecw_hasDerivAt_im (ecw_MD_trace (ecw_MD_pow hA hW ha i j x (k + 1)))
  have h := (h2.sub h1).const_mul (-(1 / Real.pi) * ((-1 : ℝ) ^ k * (k.factorial : ℝ)))
  unfold ecwPsi
  convert h using 1
  · funext t
    simp only [Pi.sub_apply]
    ring
  · have e : ∀ w : Matrix (Fin N) (Fin N) ℂ, (trace (-((k + 1 : ℕ) : ℂ) • w)).im =
        -((k : ℝ) + 1) * (trace w).im := fun w => by
      rw [Matrix.trace_smul, smul_eq_mul]
      simp [Complex.mul_im]
    rw [e, e]
    simp only [Nat.factorial_succ, pow_succ]
    push_cast
    ring

private lemma ecw_hasDerivAt_smCount_psi {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (x : ℝ) :
    HasDerivAt (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂)
      (ecwPsi A Wm η E₁ E₂ i j 0 x) x := by
  refine (hasDerivAt_smCountW hA hW hη E₁ E₂ i j x).congr_deriv ?_
  simp [ecwPsi]

private lemma ecw_iteratedDeriv_eq_psi {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (n : ℕ) :
    iteratedDeriv (n + 1) (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) =
      ecwPsi A Wm η E₁ E₂ i j n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext x
    exact (ecw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (ecw_hasDerivAt_psi hA hW hη E₁ E₂ i j n x).deriv

/-- The smoothed count is smooth in a symmetric entry. -/
private lemma ecw_contDiff_smCount {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (n : ℕ) :
    ContDiff ℝ n (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) := by
  have hP : ∀ m : ℕ, ∀ k : ℕ, ContDiff ℝ m (ecwPsi A Wm η E₁ E₂ i j k) := by
    intro m
    induction m with
    | zero =>
      intro k
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
        (ecw_hasDerivAt_psi hA hW hη E₁ E₂ i j k x).continuousAt)
    | succ m ih =>
      intro k
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun x => (ecw_hasDerivAt_psi hA hW hη E₁ E₂ i j k x).differentiableAt,
        fun h => absurd h (by simp), ?_⟩
      have : deriv (ecwPsi A Wm η E₁ E₂ i j k) = ecwPsi A Wm η E₁ E₂ i j (k + 1) :=
        funext fun x => (ecw_hasDerivAt_psi hA hW hη E₁ E₂ i j k x).deriv
      rw [this]
      exact ih (k + 1)
  cases n with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (ecw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).continuousAt)
  | succ m =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (ecw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have : deriv (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) = ecwPsi A Wm η E₁ E₂ i j 0 :=
      funext fun x => (ecw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).deriv
    rw [this]
    exact hP m 0


end Higher

/-! ## The `2 × 2` block of `tr (Δ G)^k` and bounds on the entry derivatives -/

section Block

variable {N : ℕ}


/-- The pattern of `Δ` on `(i, j)`: `[[0, 1], [1, 0]]` off the diagonal, `[[1, 0], [0, 0]]` on
it. -/
private def ecwD (i j : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = j then !![1, 0; 0, 0] else !![0, 1; 1, 0]

/-- The `2 × 2` block governing `tr (Δ B)^k`. -/
private def ecwBlk (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  ecwD i j * !![B i i, B i j; B j i, B j j]

/-- `tr (Δ B)^{k+1}` is the trace of the `(k+1)`-st power of the `2 × 2` block. -/
private lemma ecw_trace_delta_pow (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (k : ℕ) :
    trace ((deltaW i j * B) ^ (k + 1)) = trace ((ecwBlk B i j) ^ (k + 1)) := by
  set ι : Fin 2 → Fin N := ![i, j] with hι
  set P : Matrix (Fin N) (Fin 2) ℂ := Matrix.of fun s r => if s = ι r then 1 else 0 with hP
  set R : Matrix (Fin 2) (Fin N) ℂ := ecwD i j * Pᵀ * B with hR
  have hPBP : Pᵀ * B * P = !![B i i, B i j; B j i, B j j] := by
    ext r c
    have e : (Pᵀ * B * P) r c = B (ι r) (ι c) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, hP, Matrix.transpose_apply, Matrix.of_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_one,
        mul_zero]
    rw [e]
    fin_cases r <;> fin_cases c <;> simp [hι]
  have hΔ : deltaW i j = P * ecwD i j * Pᵀ := by
    ext s u
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP, Matrix.of_apply, Matrix.transpose_apply,
      ecwD, deltaW, hι]
    by_cases hij : i = j
    · subst hij
      by_cases hs : s = i <;> by_cases hu : u = i <;> simp [hs, hu]
    · by_cases hs : s = i <;> by_cases hu : u = j <;> by_cases hs' : s = j <;>
        by_cases hu' : u = i <;> simp_all
  have h1 : deltaW i j * B = P * R := by
    rw [hΔ, hR]; simp only [Matrix.mul_assoc]
  have h2 : R * P = ecwBlk B i j := by
    rw [hR, ecwBlk, ← hPBP]; simp only [Matrix.mul_assoc]
  have h3 : ∀ k : ℕ, (P * R) ^ (k + 1) = P * ((R * P) ^ k * R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h1, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ, h2]

private lemma ecw_blk_sub (B B' : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ecwBlk B i j - ecwBlk B' i j = ecwBlk (B - B') i j := by
  simp only [ecwBlk, ← Matrix.mul_sub]
  congr 1
  ext r c
  fin_cases r <;> fin_cases c <;> simp

/-- The entries of the block are entries of `B` on `{i, j}²` or zero. -/
private lemma ecw_blk_le (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) {W : ℝ} (hW0 : 0 ≤ W)
    (h1 : ‖B i i‖ ≤ W) (h2 : ‖B i j‖ ≤ W) (h3 : ‖B j i‖ ≤ W) (h4 : ‖B j j‖ ≤ W) (r c : Fin 2) :
    ‖ecwBlk B i j r c‖ ≤ W := by
  unfold ecwBlk ecwD
  split_ifs <;> fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> assumption

private lemma ecw_entry_mul_le (X Y : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℝ}
    (hX : ∀ r c, ‖X r c‖ ≤ a) (hY : ∀ r c, ‖Y r c‖ ≤ b) (r c : Fin 2) :
    ‖(X * Y) r c‖ ≤ 2 * a * b := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hX 0 0)
  have hb : 0 ≤ b := (norm_nonneg _).trans (hY 0 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  calc ‖X r 0 * Y 0 c + X r 1 * Y 1 c‖ ≤ ‖X r 0‖ * ‖Y 0 c‖ + ‖X r 1‖ * ‖Y 1 c‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ a * b + a * b := by gcongr <;> first | exact hX _ _ | exact hY _ _
    _ = 2 * a * b := by ring

private lemma ecw_pow_entry_le (X : Matrix (Fin 2) (Fin 2) ℂ) {a : ℝ}
    (hX : ∀ r c, ‖X r c‖ ≤ a) (k : ℕ) : ∀ r c, ‖(X ^ (k + 1)) r c‖ ≤ (2 * a) ^ (k + 1) := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hX 0 0)
  induction k with
  | zero =>
    intro r c
    rw [zero_add, pow_one, pow_one]
    linarith [hX r c]
  | succ k ih =>
    intro r c
    rw [pow_succ X (k + 1)]
    refine (ecw_entry_mul_le _ _ ih hX r c).trans (le_of_eq ?_)
    ring

private lemma ecw_pow_sub_entry_le (X Y : Matrix (Fin 2) (Fin 2) ℂ) {a δ : ℝ}
    (hX : ∀ r c, ‖X r c‖ ≤ a) (hY : ∀ r c, ‖Y r c‖ ≤ a) (hXY : ∀ r c, ‖(X - Y) r c‖ ≤ δ)
    (k : ℕ) : ∀ r c, ‖(X ^ (k + 1) - Y ^ (k + 1)) r c‖ ≤ 2 * (k + 1) * (2 * a) ^ k * δ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hX 0 0)
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hXY 0 0)
  induction k with
  | zero =>
    intro r c
    simp only [zero_add, pow_one, pow_zero, Nat.cast_zero]
    linarith [hXY r c]
  | succ k ih =>
    intro r c
    have e : X ^ (k + 1 + 1) - Y ^ (k + 1 + 1) =
        X ^ (k + 1) * (X - Y) + (X ^ (k + 1) - Y ^ (k + 1)) * Y := by
      rw [pow_succ X (k + 1), pow_succ Y (k + 1), Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e, Matrix.add_apply]
    have t1 := ecw_entry_mul_le _ _ (ecw_pow_entry_le X hX k) hXY r c
    have t2 := ecw_entry_mul_le _ _ ih hY r c
    refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans (le_of_eq ?_))
    push_cast
    ring

private lemma ecw_trace_two_le (X : Matrix (Fin 2) (Fin 2) ℂ) {a : ℝ}
    (hX : ∀ r c, ‖X r c‖ ≤ a) : ‖trace X‖ ≤ 2 * a := by
  rw [Matrix.trace_fin_two]
  calc ‖X 0 0 + X 1 1‖ ≤ ‖X 0 0‖ + ‖X 1 1‖ := norm_add_le _ _
    _ ≤ 2 * a := by linarith [hX 0 0, hX 1 1]

private lemma ecw_factorial_le {n : ℕ} (hn : n ≤ 4) : (n.factorial : ℝ) ≤ 24 := by
  have : n.factorial ≤ 24 := by interval_cases n <;> decide
  exact_mod_cast this

/-- `|-(1/π) (-1)^n n! (Im a - Im b)| ≤ 24 ‖a - b‖` for `n ≤ 4`. -/
private lemma ecw_coef_le {n : ℕ} (hn : n ≤ 4) (a b : ℂ) :
    |-(1 / Real.pi) * (((-1 : ℝ) ^ n * (n.factorial : ℝ)) * (a.im - b.im))| ≤ 24 * ‖a - b‖ := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : |a.im - b.im| ≤ ‖a - b‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), Nat.abs_cast]
  have hf := ecw_factorial_le hn
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hp : 1 / Real.pi ≤ 1 := by rw [div_le_one (by positivity)]; exact hpi
  calc 1 / Real.pi * ((n.factorial : ℝ) * |a.im - b.im|) ≤ 1 * (24 * ‖a - b‖) := by
        gcongr
    _ = 24 * ‖a - b‖ := one_mul _

/-- Entry bounds `|G_{st}| ≤ W` on `{i, j}²` at both window points give
`|∂^{n+1} 𝒳| ≤ (192 W)^{n+1}` for `n + 1 ≤ 5`. -/
private lemma ecw_deriv_le_crude {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (s : ℝ) {Wb : ℝ}
    (hWb : 0 ≤ Wb)
    (h₁ : ∀ a b, ‖GW A (Wupd Wm i j s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    (h₂ : ∀ a b, ‖GW A (Wupd Wm i j s) ((E₂ : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) s| ≤
      (192 * Wb) ^ (n + 1) := by
  rw [ecw_iteratedDeriv_eq_psi hA hW hη E₁ E₂ i j n]
  unfold ecwPsi
  refine (ecw_coef_le hn _ _).trans ?_
  rw [ecw_trace_delta_pow, ecw_trace_delta_pow]
  have b2 := ecw_pow_entry_le _ (ecw_blk_le _ i j hWb (h₂ _ _) (h₂ _ _) (h₂ _ _) (h₂ _ _)) n
  have b1 := ecw_pow_entry_le _ (ecw_blk_le _ i j hWb (h₁ _ _) (h₁ _ _) (h₁ _ _) (h₁ _ _)) n
  have t2 := ecw_trace_two_le _ b2
  have t1 := ecw_trace_two_le _ b1
  have h4 : (0 : ℝ) ≤ (2 * Wb) ^ (n + 1) := by positivity
  calc 24 * ‖_ - _‖ ≤ 24 * (2 * (2 * Wb) ^ (n + 1) + 2 * (2 * Wb) ^ (n + 1)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add t2 t1)
    _ = 96 * (2 * Wb) ^ (n + 1) := by ring
    _ ≤ 96 ^ (n + 1) * (2 * Wb) ^ (n + 1) := by
        gcongr
        exact le_self_pow₀ (by norm_num) (by omega)
    _ = (192 * Wb) ^ (n + 1) := by rw [← mul_pow]; ring

/-- Entry bounds `|G_{st}| ≤ W` (`W ≥ 1`) on `{i, j}²` at both window points, with differences
at most `δ` between the two points, give `|∂^{n+1} 𝒳| ≤ 480 (2W)^4 δ` for `n + 1 ≤ 5`. -/
private lemma ecw_deriv_le_small {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (s : ℝ) {Wb δ : ℝ}
    (hWb : 1 ≤ Wb)
    (h₁ : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (Wupd Wm i j s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    (h₂ : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (Wupd Wm i j s) ((E₂ : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    (hd : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (Wupd Wm i j s) ((E₂ : ℂ) + η * Complex.I) a b -
        GW A (Wupd Wm i j s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ δ)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) s| ≤
      480 * (2 * Wb) ^ 4 * δ := by
  have hi : i ∈ ({i, j} : Set (Fin N)) := Set.mem_insert _ _
  have hj : j ∈ ({i, j} : Set (Fin N)) := Set.mem_insert_of_mem _ rfl
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hd i hi i hi)
  rw [ecw_iteratedDeriv_eq_psi hA hW hη E₁ E₂ i j n]
  unfold ecwPsi
  refine (ecw_coef_le hn _ _).trans ?_
  rw [ecw_trace_delta_pow, ecw_trace_delta_pow, ← Matrix.trace_sub]
  set B₂ := GW A (Wupd Wm i j s) ((E₂ : ℂ) + η * Complex.I)
  set B₁ := GW A (Wupd Wm i j s) ((E₁ : ℂ) + η * Complex.I)
  have hb2 := ecw_blk_le B₂ i j (by linarith) (h₂ i hi i hi) (h₂ i hi j hj) (h₂ j hj i hi)
    (h₂ j hj j hj)
  have hb1 := ecw_blk_le B₁ i j (by linarith) (h₁ i hi i hi) (h₁ i hi j hj) (h₁ j hj i hi)
    (h₁ j hj j hj)
  have hbd : ∀ r c, ‖(ecwBlk B₂ i j - ecwBlk B₁ i j) r c‖ ≤ δ := by
    rw [ecw_blk_sub]
    exact ecw_blk_le _ i j hδ (by simpa using hd i hi i hi) (by simpa using hd i hi j hj)
      (by simpa using hd j hj i hi) (by simpa using hd j hj j hj)
  have he := ecw_pow_sub_entry_le _ _ hb2 hb1 hbd n
  have ht := ecw_trace_two_le _ he
  have hp : (2 * Wb) ^ n ≤ (2 * Wb) ^ 4 := pow_le_pow_right₀ (by linarith) hn
  have hn' : ((n : ℝ) + 1) ≤ 5 := by exact_mod_cast (show n + 1 ≤ 5 by omega)
  have h0 : 0 ≤ (2 * Wb) ^ n := by positivity
  calc 24 * ‖trace ((ecwBlk B₂ i j) ^ (n + 1) - (ecwBlk B₁ i j) ^ (n + 1))‖
      ≤ 24 * (2 * (2 * (n + 1) * (2 * Wb) ^ n * δ)) := by gcongr
    _ = 96 * ((n + 1) * (2 * Wb) ^ n) * δ := by ring
    _ ≤ 96 * (5 * (2 * Wb) ^ 4) * δ := by gcongr
    _ = 480 * (2 * Wb) ^ 4 * δ := by ring


end Block

/-! ## Derivatives of `F ∘ φ`, measurability and events -/

section Comp


/-- Iterated derivatives of a vector-valued function are taken componentwise. -/
private lemma ecw_iteratedDeriv_pi {l : ℕ} (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) (n : ℕ) :
    iteratedDeriv n φ = fun t j => iteratedDeriv n (fun s => φ s j) t := by
  induction n with
  | zero => funext t j; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_pi fun j => ((hφ j (n + 1)).differentiable_iteratedDeriv n
      (by exact_mod_cast Nat.lt_succ_self n)).differentiableAt]
    funext j
    rw [iteratedDeriv_succ]

/-- Faà di Bruno bound: if `‖D^m F‖ ≤ C_b` for `m ≤ k` and the `i`-th derivatives of the
components of `φ` at `t` are at most `D^i` for `1 ≤ i ≤ n ≤ k`, then
`|(F ∘ φ)^{(n)}(t)| ≤ n! C_b D^n`. -/
private lemma ecw_comp_le {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} {k : ℕ}
    (hF : ContDiff ℝ k F)
    (hFb : ∀ m ≤ k, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn : n ≤ k) (t : ℝ)
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ D ^ i) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * D ^ n := by
  have hφc : ContDiff ℝ k φ := contDiff_pi.2 fun j => hφ j k
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine norm_iteratedFDeriv_comp_le hF hφc (by exact_mod_cast hn) t
    (fun i hi => hFb i (hi.trans hn) _) fun i h1 h2 => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ecw_iteratedDeriv_pi φ hφ]
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    rw [Real.norm_eq_abs]; exact hD i h1 h2 j

/-- The same bound with one small factor: if the component derivatives of orders `1, …, n` at
`t` are at most `Θ ∈ [0, 1]`, then `|(F ∘ φ)^{(n)}(t)| ≤ n! C_b Θ`. -/
private lemma ecw_comp_le_small {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} {k : ℕ}
    (hF : ContDiff ℝ k F)
    (hFb : ∀ m ≤ k, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ k)
    (t : ℝ) {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ Θ) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * Θ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set D : ℝ := Θ ^ ((n : ℝ)⁻¹) with hDdef
  have hD0 : 0 ≤ D := Real.rpow_nonneg hΘ0 _
  have hDn : D ^ n = Θ := by
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0, inv_mul_cancel₀ hn0.ne', Real.rpow_one]
  have h := ecw_comp_le hF hFb φ hφ hn t hD0 fun i h1 h2 j => by
    refine (hD i h1 h2 j).trans ?_
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0]
    conv_lhs => rw [← Real.rpow_one Θ]
    refine Real.rpow_le_rpow_of_exponent_ge' hΘ0 hΘ1 (by positivity) ?_
    rw [inv_mul_le_iff₀ hn0, mul_one]
    exact_mod_cast h2
  rwa [hDn] at h

/-- `(∑_j A_j U_j)'' = ∑_j (A_j'' U_j + 2 A_j' U_j' + A_j U_j'')` for `C²` families. -/
private lemma ecw_deriv2_sum_mul {l : ℕ} (A U : Fin l → ℝ → ℝ)
    (hA : ∀ j, ContDiff ℝ 2 (A j)) (hU : ∀ j, ContDiff ℝ 2 (U j)) (t : ℝ) :
    deriv (deriv fun s => ∑ j, A j s * U j s) t =
      ∑ j, (deriv (deriv (A j)) t * U j t + 2 * deriv (A j) t * deriv (U j) t +
        A j t * deriv (deriv (U j)) t) := by
  have hA1 : ∀ j, Differentiable ℝ (A j) := fun j => (hA j).differentiable (by norm_num)
  have hU1 : ∀ j, Differentiable ℝ (U j) := fun j => (hU j).differentiable (by norm_num)
  have hA2 : ∀ j, Differentiable ℝ (deriv (A j)) := fun j => by
    have := (hA j).differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hU2 : ∀ j, Differentiable ℝ (deriv (U j)) := fun j => by
    have := (hU j).differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have hd : deriv (fun s => ∑ j, A j s * U j s) =
      fun s => ∑ j, (deriv (A j) s * U j s + A j s * deriv (U j) s) := by
    funext s
    exact (HasDerivAt.fun_sum fun j _ => (hA1 j s).hasDerivAt.mul (hU1 j s).hasDerivAt).deriv
  have hd2 : HasDerivAt (fun s => ∑ j, (deriv (A j) s * U j s + A j s * deriv (U j) s))
      (∑ j, ((deriv (deriv (A j)) t * U j t + deriv (A j) t * deriv (U j) t) +
        (deriv (A j) t * deriv (U j) t + A j t * deriv (deriv (U j)) t))) t :=
    HasDerivAt.fun_sum fun j _ => ((hA2 j t).hasDerivAt.mul (hU1 j t).hasDerivAt).add
      ((hA1 j t).hasDerivAt.mul (hU2 j t).hasDerivAt)
  rw [hd, hd2.deriv]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The chain rule for `F ∘ φ` with `φ : ℝ → ℝ^l`:
`(F ∘ φ)' = ∑_j ∂_j F(φ) φ_j'`. -/
private lemma ecw_deriv_comp {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F)
    (φ : ℝ → Fin l → ℝ) (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) :
    deriv (F ∘ φ) = fun t =>
      ∑ j, fderiv ℝ F (φ t) (Pi.single j 1) * deriv (fun s => φ s j) t := by
  funext t
  have hFd : HasFDerivAt F (fderiv ℝ F (φ t)) (φ t) :=
    ((hF.differentiable (by norm_num)) (φ t)).hasFDerivAt
  have hφd : DifferentiableAt ℝ φ t :=
    (contDiff_pi.2 fun j => hφ j 1).differentiable (by norm_num) t
  rw [(hFd.comp_hasDerivAt t hφd.hasDerivAt).deriv,
    deriv_pi fun j => ((hφ j 1).differentiable (by norm_num)) t]
  have hv : (fun j => deriv (fun s => φ s j) t) =
      ∑ j, deriv (fun s => φ s j) t • (Pi.single j 1 : Fin l → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single (fun j => deriv (fun s => φ s j) t)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [hv, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- The third derivative of `F ∘ φ`:
`(F ∘ φ)''' = ∑_j ((∂_j F ∘ φ)'' φ_j' + 2 (∂_j F ∘ φ)' φ_j'' + ∂_j F(φ) φ_j''')`. -/
private lemma ecw_iteratedDeriv_three_comp {l : ℕ} {F : (Fin l → ℝ) → ℝ}
    (hF : ContDiff ℝ 5 F) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) (t : ℝ) :
    iteratedDeriv 3 (F ∘ φ) t = ∑ j,
      (iteratedDeriv 2 (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) t *
          iteratedDeriv 1 (fun s => φ s j) t +
        2 * iteratedDeriv 1 (fun s => fderiv ℝ F (φ s) (Pi.single j 1)) t *
          iteratedDeriv 2 (fun s => φ s j) t +
        fderiv ℝ F (φ t) (Pi.single j 1) * iteratedDeriv 3 (fun s => φ s j) t) := by
  have h2 : ∀ g : ℝ → ℝ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h3 : ∀ g : ℝ → ℝ, iteratedDeriv 3 g = deriv (deriv (deriv g)) := fun g => by
    rw [iteratedDeriv_succ, h2]
  have hg : ∀ j : Fin l, ContDiff ℝ 4 fun s => fderiv ℝ F (φ s) (Pi.single j 1) := fun j =>
    ((hF.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const).comp
      (contDiff_pi.2 fun j => hφ j 4)
  have hu : ∀ j : Fin l, ContDiff ℝ 2 (deriv fun s => φ s j) := fun j => by
    have := (hφ j 3).iterate_deriv' 2 1
    simpa using this
  rw [iteratedDeriv_succ', ecw_deriv_comp hF φ hφ, h2,
    ecw_deriv2_sum_mul _ _ (fun j => (hg j).of_le (by norm_num)) hu]
  simp only [h2, h3, iteratedDeriv_one]

/-- The partial derivatives `∂_j F = DF(·) e_j` satisfy `‖D^m ∂_j F‖ ≤ C_b` for `m ≤ 4`. -/
private lemma ecw_partial_bound {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ}
    (hF : ContDiff ℝ 5 F) (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (j : Fin l) :
    ∀ m ≤ 4, ∀ x, ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ F x (Pi.single j 1)) x‖ ≤ Cb := by
  intro m hm x
  set L : ((Fin l → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ)) with hLdef
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
    rw [hLdef, ContinuousLinearMap.apply_apply, one_mul]
    calc ‖A (Pi.single j 1)‖ ≤ ‖A‖ * ‖(Pi.single j 1 : Fin l → ℝ)‖ := A.le_opNorm _
      _ = ‖A‖ := by rw [Pi.norm_single, norm_one, mul_one]
  have e : (fun x => fderiv ℝ F x (Pi.single j 1)) = L ∘ fderiv ℝ F := rfl
  rw [e]
  have hFd : ContDiff ℝ 4 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  refine (L.norm_iteratedFDeriv_comp_left hFd.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc ‖L‖ * ‖iteratedFDeriv ℝ (m + 1) F x‖ ≤ 1 * Cb :=
        mul_le_mul hL (hFb _ (by omega) x) (norm_nonneg _) zero_le_one
    _ = Cb := one_mul _

/-- Measurability of the iterated derivatives in a parameter, from the joint measurability of
the function and its smoothness in the variable. -/
private lemma ecw_measurable_iteratedDeriv {α : Type*} [MeasurableSpace α] (φ : α → ℝ → ℝ)
    (hφ : Measurable fun p : α × ℝ => φ p.1 p.2) (m : ℕ) (hd : ∀ a, ContDiff ℝ m (φ a)) :
    ∀ n ≤ m, Measurable fun p : α × ℝ => iteratedDeriv n (φ p.1) p.2 := by
  intro n
  induction n with
  | zero => intro _; simpa using hφ
  | succ n ih =>
    intro hn
    have ihn := ih (Nat.le_of_succ_le hn)
    have hdiff : ∀ a, Differentiable ℝ (iteratedDeriv n (φ a)) := fun a =>
      (hd a).differentiable_iteratedDeriv n (by exact_mod_cast hn)
    have hshift : ∀ c : ℝ, Measurable fun p : α × ℝ => iteratedDeriv n (φ p.1) (p.2 + c) :=
      fun c => ihn.comp (measurable_fst.prodMk (measurable_snd.add_const c))
    refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) (p : α × ℝ) =>
      ((k : ℝ) + 1) * (iteratedDeriv n (φ p.1) (p.2 + 1 / ((k : ℝ) + 1)) -
        iteratedDeriv n (φ p.1) p.2)) (fun k => measurable_const.mul ((hshift _).sub ihn)) ?_
    rw [tendsto_pi_nhds]
    intro p
    have hder := ((hdiff p.1) p.2).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hder
    have hu : Tendsto (fun k : ℕ => p.2 + 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] p.2) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds (x := p.2)).add h0
      · exact Eventually.of_forall fun k => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
          positivity
    have h := hder.comp hu
    rw [iteratedDeriv_succ]
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, slope, vsub_eq_sub, smul_eq_mul, add_sub_cancel_left,
      one_div, inv_inv]

/-- `c N^y ≤ 1/2` eventually, for `y < 0`. -/
private lemma ecw_ev_small {y : ℝ} (hy : y < 0) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ y ≤ 1 / 2 := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ y) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -y) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun N : ℕ => c * (N : ℝ) ^ y) atTop (𝓝 0) := by
    simpa using h1.const_mul c
  exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le

/-- `N^x ≤ N^y` for `x ≤ y`, `N ≥ 1`. -/
private lemma ecw_rpow_le {N : ℕ} (hN : 1 ≤ N) {x y : ℝ} (h : x ≤ y) :
    (N : ℝ) ^ x ≤ (N : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

/-- Union bound for finitely many events of probability `≥ 1 - q`: a nonnegative integrable
`T` with `E T ≤ |ι| q` such that at every point either all events hold or `T ≥ 1`. -/
private lemma ecw_events {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {ι : Type*} [Fintype ι] (P : ι → Set Ω) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ b, (ℙ : Measure Ω) (P b)ᶜ ≤ ENNReal.ofReal q) :
    ∃ T : Ω → ℝ, (∀ ω, 0 ≤ T ω) ∧ Integrable T ∧ ∫ ω, T ω ≤ Fintype.card ι * q ∧
      ∀ ω, (∀ b, ω ∈ P b) ∨ 1 ≤ T ω := by
  set Q : ι → Set Ω := fun b => toMeasurable (ℙ : Measure Ω) (P b)ᶜ with hQ
  have hQm : ∀ b, MeasurableSet (Q b) := fun b => measurableSet_toMeasurable _ _
  have hind0 : ∀ b ω, 0 ≤ (Q b).indicator (1 : Ω → ℝ) ω := fun b ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hindi : ∀ b ∈ (Finset.univ : Finset ι), Integrable ((Q b).indicator (1 : Ω → ℝ)) :=
    fun b _ => (integrable_const (1 : ℝ)).indicator (hQm b)
  refine ⟨fun ω => ∑ b, (Q b).indicator 1 ω, fun ω => Finset.sum_nonneg fun b _ => hind0 b ω,
    integrable_finsetSum _ hindi, ?_, fun ω => ?_⟩
  · rw [integral_finsetSum _ hindi]
    calc ∑ b, ∫ ω, (Q b).indicator (1 : Ω → ℝ) ω = ∑ b, (ℙ : Measure Ω).real (Q b) :=
          Finset.sum_congr rfl fun b _ => integral_indicator_one (hQm b)
      _ ≤ ∑ _b : ι, q := Finset.sum_le_sum fun b _ => by
          rw [measureReal_def, hQ, measure_toMeasurable]
          exact ENNReal.toReal_le_of_le_ofReal hq (hP _)
      _ = Fintype.card ι * q := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · by_cases h : ∀ b, ω ∈ P b
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨b, hb⟩ := h
      have hmem : ω ∈ Q b := subset_toMeasurable _ _ hb
      have h1 : (Q b).indicator (1 : Ω → ℝ) ω = 1 := by
        rw [Set.indicator_of_mem hmem, Pi.one_apply]
      have hle := Finset.single_le_sum (f := fun b => (Q b).indicator (1 : Ω → ℝ) ω)
        (fun b _ => hind0 b ω) (Finset.mem_univ b)
      linarith


end Comp

/-! ## The entry function of a Wigner matrix -/

section WignerEntry

variable {N : ℕ}


/-- The symmetric matrix read off the upper triangle of `W`. -/
private def ecwSym (Wm : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun s u => if s ≤ u then Wm s u else Wm u s

private lemma ecw_sym_symm (Wm : Matrix (Fin N) (Fin N) ℝ) : (ecwSym Wm)ᵀ = ecwSym Wm := by
  ext s u
  simp only [Matrix.transpose_apply, ecwSym]
  rcases lt_trichotomy s u with h | rfl | h
  · simp [not_le.2 h, h.le]
  · rfl
  · simp [not_le.2 h, h.le]

private lemma ecw_sym_herm (Wm : Matrix (Fin N) (Fin N) ℝ) : (ecwSym Wm).IsHermitian :=
  ecw_herm_of_symm (ecw_sym_symm Wm)

private lemma ecw_sym_eq {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm) : ecwSym Wm = Wm := by
  ext s u
  simp only [ecwSym]
  split_ifs
  · rfl
  · have := congrFun (congrFun hW s) u
    simpa [Matrix.transpose_apply] using this

private lemma ecw_continuous_sym : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ => ecwSym Wm := by
  refine continuous_matrix fun s u => ?_
  by_cases h : s ≤ u
  · simpa [ecwSym, h] using continuous_id.matrix_elem s u
  · simpa [ecwSym, h] using continuous_id.matrix_elem u s

/-- The function `t ↦ F(𝒳(W^{t}_{(ij)} + A))` of the entry `(i, j)`, `W` read off its upper
triangle. -/
private def ecwf {l : ℕ} (F : (Fin l → ℝ) → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) (Wm : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) : ℝ :=
  smFW F A (Wupd (ecwSym Wm) i j t) η Ea Eb

private lemma ecw_f_contDiff {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) (Wm : Matrix (Fin N) (Fin N) ℝ) :
    ContDiff ℝ 5 (ecwf F A η Ea Eb i j Wm) :=
  hF.comp (contDiff_pi.2 fun k =>
    ecw_contDiff_smCount hA (ecw_sym_herm Wm) hη (Ea k) (Eb k) i j 5)

private lemma ecw_f_continuous {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => ecwf F A η Ea Eb i j q.1 q.2 := by
  have hW : Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => Wupd (ecwSym q.1) i j q.2 :=
    (ecw_continuous_Wupd i j).comp ((ecw_continuous_sym.comp continuous_fst).prodMk
      continuous_snd)
  have hc : ∀ E₁ E₂ : ℝ, Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ =>
      smCount (Wupd (ecwSym q.1) i j q.2 + A) η E₁ E₂ := by
    intro E₁ E₂
    have he : (fun q : Matrix (Fin N) (Fin N) ℝ × ℝ =>
        smCount (Wupd (ecwSym q.1) i j q.2 + A) η E₁ E₂) = fun q => Real.pi⁻¹ *
          ∫ y in E₁..E₂,
            (trace (GW A (Wupd (ecwSym q.1) i j q.2) ((y : ℂ) + η * Complex.I))).im := by
      funext q
      exact ecw_smCount_eq (ecw_Wupd_herm hA (ecw_sym_herm q.1) i j q.2) hη E₁ E₂
    rw [he]
    refine continuous_const.mul ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : Matrix (Fin N) (Fin N) ℝ × ℝ) (y : ℝ) =>
        (trace (GW A (Wupd (ecwSym q.1) i j q.2) ((y : ℂ) + η * Complex.I))).im) ?_ E₁ E₂
    have hG := ecw_continuous_GW A (Wf := fun p : (Matrix (Fin N) (Fin N) ℝ × ℝ) × ℝ =>
        Wupd (ecwSym p.1.1) i j p.1.2)
      (zf := fun p : (Matrix (Fin N) (Fin N) ℝ × ℝ) × ℝ => ((p.2 : ℝ) : ℂ) + η * Complex.I)
      (hW.comp continuous_fst)
      ((Complex.continuous_ofReal.comp continuous_snd).add continuous_const)
      (fun p : (Matrix (Fin N) (Fin N) ℝ × ℝ) × ℝ =>
        ecw_Wupd_herm hA (ecw_sym_herm p.1.1) i j p.1.2) fun _ => by simpa using hη
    exact Complex.continuous_im.comp hG.matrix_trace
  exact hF.continuous.comp (continuous_pi fun k => hc (Ea k) (Eb k))

/-- An entry of a matrix is at most its operator norm. -/
private lemma ecw_entry_le_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (s t : ι) : ‖A s t‖ ≤ ‖A‖ := by
  have h1 := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (Pi.single t (1 : ℂ)))
  have h2 : ‖(WithLp.toLp 2 (Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι)‖ = 1 := by
    simp
  have h3 : ‖A s t‖ ≤ ‖(WithLp.toLp 2 (A *ᵥ Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι)‖ := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 (A *ᵥ Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι) s
    simpa [mulVec_single_one] using this
  rw [h2, mul_one] at h1
  exact h3.trans h1

private lemma ecw_testBilin_single (B : Matrix (Fin N) (Fin N) ℂ) (s t : Fin N) :
    testBilin (Pi.single s 1) B (Pi.single t 1) = B s t := by
  simp only [testBilin, dotProduct, mulVec, Pi.single_apply]
  simp [apply_ite, ite_mul, Finset.sum_ite_eq']

private lemma ecw_testNorm_single (s : Fin N) : testNorm (Pi.single s (1 : ℝ)) = 1 := by
  simp [testNorm, Pi.single_apply]

/-- The deterministic bound `|∂ⁿ f| ≤ n! C_b (192/η)^n`, `n ≤ 5`, uniformly in `W`. -/
private lemma ecw_crude {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η) (Ea Eb : Fin l → ℝ) (i j : Fin N)
    (Wm : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) {n : ℕ} (hn : n ≤ 5) :
    |iteratedDeriv n (ecwf F A η Ea Eb i j Wm) s| ≤ n.factorial * Cb * (192 * (1 / η)) ^ n := by
  have hgvc : ∀ (k : Fin l) (n : ℕ), ContDiff ℝ n fun t =>
      smCount (Wupd (ecwSym Wm) i j t + A) η (Ea k) (Eb k) := fun k n =>
    ecw_contDiff_smCount hA (ecw_sym_herm Wm) hη (Ea k) (Eb k) i j n
  refine ecw_comp_le hF hFb (fun t k => smCount (Wupd (ecwSym Wm) i j t + A) η (Ea k) (Eb k))
    hgvc hn s (by positivity) fun i' h1 h2 k => ?_
  obtain ⟨n', rfl⟩ : ∃ n', i' = n' + 1 := ⟨i' - 1, by omega⟩
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * Complex.I).im := fun E => by simpa using hη
  have hb : ∀ E : ℝ, ∀ a b, ‖GW A (Wupd (ecwSym Wm) i j s) ((E : ℂ) + η * Complex.I) a b‖ ≤
      1 / η := fun E a b => by
    have := ecw_GW_entry_le (ecw_Wupd_herm hA (ecw_sym_herm Wm) i j s) (hz E) a b
    simpa using this
  exact ecw_deriv_le_crude hA (ecw_sym_herm Wm) hη (Ea k) (Eb k) i j s (by positivity)
    (hb (Ea k)) (hb (Eb k)) (by omega)


end WignerEntry

/-! ## The comparison window -/

section Window

variable {N : ℕ}


/-- The comparison window: for `N ≥ N₀`, `‖A‖ ≤ τ⁻¹ − 3` and the standing bound, each point
`E + iη`, `η = N^{-2/3-9ε}`, `|E − L₊| ≤ 3N^{-2/3+ε}`, lies in `edgeWinW` and has
`Ψ^W ≤ c_Ψ N^{-1/3+9ε}`; and `‖Π^W(E' + iη) − Π^W(E + iη)‖ ≤ K N^{-1/3+21ε/2}`. -/
private lemma ecw_window {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) :
    ∃ cψ Kp : ℝ, 0 ≤ cψ ∧ 0 ≤ Kp ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ A : Matrix (Fin N) (Fin N) ℝ, A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 →
      StandingBoundW τ (specOf A) (domW τ N) →
      (∀ E : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        (E : ℂ) + (etaE N ε : ℝ) * Complex.I ∈ edgeWinW τ N (specOf A) ε ∧
          PsiW (specOf A) ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) ≤
            cψ * (N : ℝ) ^ (-1 / 3 + 9 * ε)) ∧
      (∀ E E' : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        |E' - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
        ‖piW A (E' + etaE N ε * Complex.I) - piW A (E + etaE N ε * Complex.I)‖ ≤
          Kp * (N : ℝ) ^ (-1 / 3 + 21 * ε / 2)) := by
  obtain ⟨cs, Ks, hcs, hKs, N₃, hsq⟩ := im_mW_sqrt_edge hτ
  obtain ⟨Kp, N₂, hpi⟩ := piW_edgeWin_sub hτ hτ4 hε hε1
  have hy : -2 / 3 + ε < 0 := by linarith
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 ((ecw_ev_small hy 6).and (ecw_ev_small hy (8 / cs)))
  refine ⟨Real.sqrt (2 * Ks) + 1, max Kp 0, by positivity, le_max_right _ _,
    max (max N₂ N₃) (max N₄ 1), le_max_of_le_right (le_max_right _ _),
    fun N hN A hA hnA hSB => ⟨fun E hE => ?_, fun E E' hE hE' => ?_⟩⟩
  rotate_left
  · have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hn : (0 : ℝ) ≤ (N : ℝ) ^ (-1 / 3 + 21 * ε / 2) := by positivity
    exact (hpi N hN2 A hA hnA hSB E E' hE hE').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4 : N₄ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hw6, hwc⟩ := hN₄ N hN4
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : (0 : ℝ) < N := by linarith
  set w : ℝ := (N : ℝ) ^ (-2 / 3 + ε) with hw
  set η : ℝ := etaE N ε with hηdef
  have hw0 : 0 < w := by positivity
  have hη0 : 0 < η := by rw [hηdef, etaE]; positivity
  have hηw : η ≤ w := by
    rw [hηdef, etaE, hw]; exact ecw_rpow_le hN1 (by linarith)
  have hη1 : η ≤ 1 := by
    rw [hηdef, etaE]; exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hw3 : 3 * w ≤ 1 := by linarith
  have hw4 : 4 * w ≤ cs := by
    have h1 : 8 / cs * w ≤ 1 / 2 := hwc
    rw [div_mul_eq_mul_div, div_le_iff₀ hcs] at h1
    linarith
  set a := specOf A with ha_def
  have ha3 : ∀ k, |a k| ≤ τ⁻¹ - 3 := fun k => (abs_specOf_le_norm hA k).trans hnA
  have ha : ∀ k, |a k| ≤ τ⁻¹ - 2 := fun k => by linarith [ha3 k]
  have hL : |LpW a| ≤ τ⁻¹ - 3 + 2 := abs_LpW_le hN1 ha3
  have hτ4' : 4 ≤ τ⁻¹ := by rw [le_inv_comm₀ (by norm_num) hτ]; linarith
  set z : ℂ := (E : ℂ) + (η : ℝ) * Complex.I with hz
  have hzre : z.re = E := by simp [hz]
  have hzim : z.im = η := by simp [hz]
  have hE' : |E| ≤ τ⁻¹ := by
    have := abs_sub_abs_le_abs_sub E (LpW a)
    linarith
  refine ⟨⟨⟨by rw [hzim]; exact hη0, by rw [hzre]; exact hE', ?_, ?_⟩, by rw [hzim], ?_⟩, ?_⟩
  · rw [hzim, hηdef, etaE]
    exact ecw_rpow_le hN1 (by linarith)
  · rw [hzim]; linarith
  · rw [hzre]; exact hE
  -- the bound on `Ψ`
  have hzc : ‖z - (LpW a : ℂ)‖ ≤ cs := by
    have e : z - (LpW a : ℂ) = ((E - LpW a : ℝ) : ℂ) + (η : ℝ) * Complex.I := by
      rw [hz]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos hη0]
    linarith
  obtain ⟨hle, hge⟩ := hsq N hN3 a ha hSB z (by rw [hzim]; exact hη0) hzc
  have hsw : Real.sqrt (4 * w) = 2 * (N : ℝ) ^ (-1 / 3 + ε / 2) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), hw, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
    congr 2
    ring
  have him : (mW a z).im ≤ Ks * (2 * (N : ℝ) ^ (-1 / 3 + ε / 2)) := by
    rw [← hsw]
    by_cases hEL : z.re ≤ LpW a
    · refine (hle hEL).2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hKs.le)
      rw [hzre, hzim]
      have := le_abs_self (LpW a - E)
      rw [abs_sub_comm] at this
      linarith
    · push Not at hEL
      refine (hge hEL.le).2.trans (mul_le_mul_of_nonneg_left ?_ hKs.le)
      rw [hzre, hzim]
      have h1 : Real.sqrt η ≤ Real.sqrt (E - LpW a + η) := Real.sqrt_le_sqrt (by linarith)
      have h2 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
      calc η / Real.sqrt (E - LpW a + η) ≤ η / Real.sqrt η :=
            div_le_div_of_nonneg_left hη0.le h2 h1
        _ = Real.sqrt η := Real.div_sqrt
        _ ≤ Real.sqrt (4 * w) := Real.sqrt_le_sqrt (by linarith)
  have hNη : (N : ℝ) * η = (N : ℝ) ^ (1 / 3 - 9 * ε) := by
    rw [hηdef, etaE, show (1 / 3 - 9 * ε : ℝ) = 1 + (-2 / 3 - 9 * ε) by ring,
      Real.rpow_add hn, Real.rpow_one]
  have hinv : 1 / ((N : ℝ) * η) = (N : ℝ) ^ (-1 / 3 + 9 * ε) := by
    rw [hNη, one_div, ← Real.rpow_neg hn.le]
    congr 1; ring
  have hq0 : 0 ≤ (N : ℝ) ^ (-1 / 3 + 9 * ε) := by positivity
  have hfrac : (mW a z).im / ((N : ℝ) * η) ≤ 2 * Ks * ((N : ℝ) ^ (-1 / 3 + 9 * ε)) ^ 2 := by
    rw [div_eq_mul_one_div, hinv]
    have h1 : (N : ℝ) ^ (-1 / 3 + ε / 2) ≤ (N : ℝ) ^ (-1 / 3 + 9 * ε) :=
      ecw_rpow_le hN1 (by linarith)
    calc (mW a z).im * (N : ℝ) ^ (-1 / 3 + 9 * ε)
        ≤ Ks * (2 * (N : ℝ) ^ (-1 / 3 + ε / 2)) * (N : ℝ) ^ (-1 / 3 + 9 * ε) :=
          mul_le_mul_of_nonneg_right him hq0
      _ ≤ Ks * (2 * (N : ℝ) ^ (-1 / 3 + 9 * ε)) * (N : ℝ) ^ (-1 / 3 + 9 * ε) := by gcongr
      _ = 2 * Ks * ((N : ℝ) ^ (-1 / 3 + 9 * ε)) ^ 2 := by ring
  unfold PsiW
  rw [hzim, hinv]
  have hs : Real.sqrt ((mW a z).im / ((N : ℝ) * η)) ≤
      Real.sqrt (2 * Ks) * (N : ℝ) ^ (-1 / 3 + 9 * ε) := by
    refine (Real.sqrt_le_sqrt hfrac).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hq0]
  linarith


end Window

/-! ## The third entry derivative at `W` -/

section ThirdEntry

variable {N : ℕ}

/-- `P_{ij}(B) = 2 B_{ij}³ + 6 B_{ij} B_{ii} B_{jj}`, the trace `tr (Δ B)³` for `i ≠ j` and a
symmetric `B`. -/
private def ecwP (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ℂ :=
  2 * B i j ^ 3 + 6 * B i j * (B i i * B j j)

/-- `tr (Δ B)³ = 2 B_{ij}³ + 6 B_{ij} B_{ii} B_{jj}` for `i ≠ j` and `B_{ji} = B_{ij}`. -/
private lemma ecw_trace_cube (B : Matrix (Fin N) (Fin N) ℂ) {i j : Fin N} (hij : i ≠ j)
    (hB : B j i = B i j) : trace ((deltaW i j * B) ^ (2 + 1)) = ecwP B i j := by
  rw [ecw_trace_delta_pow]
  simp only [ecwBlk, ecwD, hij, ↓reduceIte, pow_succ, pow_zero, Matrix.one_mul,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, ecwP]
  simp [hB]
  ring

/-- The third entry derivative of `F(𝒳)` at `W` itself, `i ≠ j`: if at both window points the
entries of `G^W` on `{i, j}²` are at most `W_b ≥ 1` and differ by at most `δ`, and
`480 (2W_b)⁴ δ ≤ Θ ≤ 1`, then `∂³_{ij} F(𝒳)` is `∑_k ∂_k F(𝒳) ∂³_{ij} 𝒳_k`, with
`∂³_{ij} 𝒳_k = -(2/π) Im[P_{ij}(G)]_{z_a}^{z_b}`, up to `4 l C_b Θ²`. -/
private lemma ecw_entry {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ}
    (hF : ContDiff ℝ 5 F) (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb)
    (Ea Eb : Fin l → ℝ) {i j : Fin N} (hij : i ≠ j) {Wb δ Θ : ℝ} (hWb : 1 ≤ Wb) (hδ : 0 ≤ δ)
    (h₁ : ∀ k, ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A Wm ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    (h₂ : ∀ k, ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A Wm ((Eb k : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    (hd : ∀ k, ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A Wm ((Eb k : ℂ) + η * Complex.I) a b - GW A Wm ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ δ)
    (hΘ : 480 * (2 * Wb) ^ 4 * δ ≤ Θ) (hΘ1 : Θ ≤ 1) :
    |smTW 3 F A Wm η Ea Eb i j (Wm i j) -
        ∑ k, fderiv ℝ F (fun k' => smCount (Wm + A) η (Ea k') (Eb k')) (Pi.single k 1) *
          (-(1 / Real.pi) * (2 * ((ecwP (GW A Wm ((Eb k : ℂ) + η * Complex.I)) i j).im -
            (ecwP (GW A Wm ((Ea k : ℂ) + η * Complex.I)) i j).im)))| ≤
      l * (Cb * (4 * Θ ^ 2)) := by
  have hWs := ecw_symm_of_herm hW
  have hself := ecw_Wupd_self hWs i j
  set φ : ℝ → Fin l → ℝ := fun t k => smCount (Wupd Wm i j t + A) η (Ea k) (Eb k) with hφdef
  have hφ : ∀ (k : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t k := fun k n =>
    ecw_contDiff_smCount hA hW hη (Ea k) (Eb k) i j n
  have hφ0 : φ (Wm i j) = fun k' => smCount (Wm + A) η (Ea k') (Eb k') := by
    simp only [hφdef, hself]
  have hT : smTW 3 F A Wm η Ea Eb i j (Wm i j) = iteratedDeriv 3 (F ∘ φ) (Wm i j) := rfl
  have hΘ0 : 0 ≤ Θ := le_trans (by positivity) hΘ
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hH : (Wm + A).IsHermitian := hW.add hA
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * Complex.I).im := fun E => by simpa using hη
  have hsym : ∀ E : ℝ, GW A Wm ((E : ℂ) + η * Complex.I) j i =
      GW A Wm ((E : ℂ) + η * Complex.I) i j := fun E => by
    have h := congrFun (congrFun (ecw_GW_transpose hH (hz E)) i) j
    rw [Matrix.transpose_apply] at h
    exact h
  -- the entry derivatives of `𝒳`
  have hder : ∀ (k : Fin l) (n : ℕ), 1 ≤ n → n ≤ 5 →
      |iteratedDeriv n (fun s => φ s k) (Wm i j)| ≤ Θ := by
    intro k n hn1 hn5
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    refine (ecw_deriv_le_small hA hW hη (Ea k) (Eb k) i j (Wm i j) (Wb := Wb) (δ := δ) hWb
      ?_ ?_ ?_ (by omega)).trans hΘ
    · rw [hself]; exact h₁ k
    · rw [hself]; exact h₂ k
    · rw [hself]; exact hd k
  -- the derivatives of `∂_k F ∘ φ`
  have hgc : ∀ k : Fin l, ContDiff ℝ 4 fun x : Fin l → ℝ => fderiv ℝ F x (Pi.single k 1) :=
    fun k => (hF.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const
  have hgd : ∀ (k : Fin l) (n : ℕ), 1 ≤ n → n ≤ 2 →
      |iteratedDeriv n (fun s => fderiv ℝ F (φ s) (Pi.single k 1)) (Wm i j)| ≤
        n.factorial * Cb * Θ := fun k n hn1 hn2 =>
    ecw_comp_le_small (k := 4) (hgc k) (ecw_partial_bound hF hFb k) φ hφ hn1 (by omega)
      (Wm i j) hΘ0 hΘ1 fun i' h1 h2 k' => hder k' i' h1 (by omega)
  have hg0 : ∀ k : Fin l, |fderiv ℝ F (fun k' => smCount (Wm + A) η (Ea k') (Eb k'))
      (Pi.single k 1)| ≤ Cb := fun k => by
    have h := ecw_partial_bound hF hFb k 0 (by norm_num)
      (fun k' => smCount (Wm + A) η (Ea k') (Eb k'))
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  -- the third derivative of `𝒳`
  have hU3 : ∀ k : Fin l, iteratedDeriv 3 (fun s => φ s k) (Wm i j) =
      -(1 / Real.pi) * (2 * ((ecwP (GW A Wm ((Eb k : ℂ) + η * Complex.I)) i j).im -
        (ecwP (GW A Wm ((Ea k : ℂ) + η * Complex.I)) i j).im)) := by
    intro k
    have h := congrFun (ecw_iteratedDeriv_eq_psi hA hW hη (Ea k) (Eb k) i j 2) (Wm i j)
    change iteratedDeriv 3 (fun s => φ s k) (Wm i j) = _ at h
    rw [h]
    unfold ecwPsi
    rw [hself, ecw_trace_cube _ hij (hsym _), ecw_trace_cube _ hij (hsym _)]
    norm_num [Nat.factorial]
  -- the assembly
  rw [hT, ecw_iteratedDeriv_three_comp hF φ hφ, hφ0, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |_| ≤ ∑ _k : Fin l, Cb * (4 * Θ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := hgd k 1 le_rfl (by norm_num)
        have h2 := hgd k 2 (by norm_num) le_rfl
        have u1 := hder k 1 le_rfl (by norm_num)
        have u2 := hder k 2 (by norm_num) (by norm_num)
        rw [hU3 k]
        set A2 := iteratedDeriv 2 (fun s => fderiv ℝ F (φ s) (Pi.single k 1)) (Wm i j)
        set A1 := iteratedDeriv 1 (fun s => fderiv ℝ F (φ s) (Pi.single k 1)) (Wm i j)
        set U1 := iteratedDeriv 1 (fun s => φ s k) (Wm i j)
        set U2 := iteratedDeriv 2 (fun s => φ s k) (Wm i j)
        set c := fderiv ℝ F (fun k' => smCount (Wm + A) η (Ea k') (Eb k')) (Pi.single k 1)
        set Mk := -(1 / Real.pi) * (2 * ((ecwP (GW A Wm ((Eb k : ℂ) + η * Complex.I)) i j).im -
            (ecwP (GW A Wm ((Ea k : ℂ) + η * Complex.I)) i j).im))
        have e : A2 * U1 + 2 * A1 * U2 + c * Mk - c * Mk = A2 * U1 + 2 * A1 * U2 := by ring
        rw [e]
        norm_num [Nat.factorial] at h1 h2
        have hA2U1 : |A2 * U1| ≤ 2 * Cb * Θ * Θ := by
          rw [abs_mul]; exact mul_le_mul h2 u1 (abs_nonneg _) (by positivity)
        have hA1U2 : |2 * A1 * U2| ≤ 2 * (Cb * Θ * Θ) := by
          rw [abs_mul, abs_mul, abs_two, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 u2 (abs_nonneg _) (by positivity))
            (by norm_num : (0 : ℝ) ≤ 2)
        calc |A2 * U1 + 2 * A1 * U2| ≤ |A2 * U1| + |2 * A1 * U2| := abs_add_le _ _
          _ ≤ 2 * Cb * Θ * Θ + 2 * (Cb * Θ * Θ) := add_le_add hA2U1 hA1U2
          _ = Cb * (4 * Θ ^ 2) := by ring
    _ = l * (Cb * (4 * Θ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end ThirdEntry
/-! ## Sums of entries -/

section Sums

variable {N : ℕ}

/-- Cauchy–Schwarz: `∑_j |x_j| ≤ √N (∑_j |x_j|²)^{1/2}`. -/
private lemma ecw_cs (x : Fin N → ℂ) :
    ∑ j, ‖x j‖ ≤ Real.sqrt N * Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := fun j => ‖x j‖)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
  have h0 : 0 ≤ ∑ j, ‖x j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  calc ∑ j, ‖x j‖ = |∑ j, ‖x j‖| := (abs_of_nonneg h0).symm
    _ ≤ Real.sqrt (N * ∑ j, ‖x j‖ ^ 2) := Real.abs_le_sqrt h

/-- `X ≤ p √X` with `p ≥ 0` gives `X ≤ p²`. -/
private lemma ecw_le_sq_of_le_mul_sqrt {X p : ℝ} (hX : 0 ≤ X) (hp : 0 ≤ p)
    (h : X ≤ p * Real.sqrt X) : X ≤ p ^ 2 := by
  have hs := Real.sq_sqrt hX
  have hs0 := Real.sqrt_nonneg X
  rcases hs0.lt_or_eq with hpos | hzero
  · have : Real.sqrt X ≤ p := by nlinarith
    nlinarith
  · have hX0 : X = 0 := by rw [← hs, ← hzero]; ring
    rw [hX0]; positivity

/-- A row of a matrix has Euclidean norm at most the operator norm. -/
private lemma ecw_row_op (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    ∑ j, ‖B i j‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  set v : Fin N → ℂ := fun j => star (B i j) with hv
  have h1 := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 v)
  have h2 : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ = Real.sqrt (∑ j, ‖B i j‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [hv]
  have h3 : ‖(B *ᵥ v) i‖ ≤ ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin N))‖ := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin N)) i
    simpa using this
  have h4 : (B *ᵥ v) i = ((∑ j, ‖B i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, hv]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have h5 : ∑ j, ‖B i j‖ ^ 2 ≤ ‖B‖ * Real.sqrt (∑ j, ‖B i j‖ ^ 2) := by
    have h6 := h3.trans h1
    rw [h4, h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)] at h6
    exact h6
  exact ecw_le_sq_of_le_mul_sqrt (Finset.sum_nonneg fun j _ => by positivity) (norm_nonneg _) h5

/-- `⟨e_i, B w⟩ = ∑_t B_{it} w_t`. -/
private lemma ecw_testBilin_single_left (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (w : Fin N → ℝ) : testBilin (Pi.single i 1) B w = ∑ t, B i t * (w t : ℂ) := by
  simp only [testBilin, dotProduct, mulVec, Pi.single_apply]
  simp [apply_ite, ite_mul, Finset.sum_ite_eq']

/-- The rows of `P` with `|⟨v, P w⟩| ≤ p |v| |w|` satisfy `∑_j |P_{ij}|² ≤ 2p²`. -/
private lemma ecw_row_pi {P : Matrix (Fin N) (Fin N) ℂ} {p : ℝ} (hp : 0 ≤ p)
    (hP : ∀ v w : Fin N → ℝ, ‖testBilin v P w‖ ≤ p * testNorm v * testNorm w) (i : Fin N) :
    ∑ j, ‖P i j‖ ^ 2 ≤ 2 * p ^ 2 := by
  have hn1 : testNorm (Pi.single i (1 : ℝ)) = 1 := ecw_testNorm_single i
  have key : ∀ f : ℂ → ℝ, (f = Complex.re ∨ f = Complex.im) →
      ∑ j, f (P i j) ^ 2 ≤ p ^ 2 := by
    intro f hf
    set w : Fin N → ℝ := fun j => f (P i j) with hw
    have hX : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hb := hP (Pi.single i 1) w
    rw [hn1, mul_one, ecw_testBilin_single_left] at hb
    have hfle : ∑ j, w j ^ 2 ≤ ‖∑ t, P i t * (w t : ℂ)‖ := by
      rcases hf with rfl | rfl
      · have e : (∑ t, P i t * (w t : ℂ)).re = ∑ j, w j ^ 2 := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hw, sq]
        rw [← e]
        exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      · have e : (∑ t, P i t * (w t : ℂ)).im = ∑ j, w j ^ 2 := by
          rw [Complex.im_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hw, sq]
        rw [← e]
        exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
    have h := hfle.trans hb
    exact ecw_le_sq_of_le_mul_sqrt hX hp (by simpa [testNorm, hw] using h)
  have hre := key Complex.re (Or.inl rfl)
  have him := key Complex.im (Or.inr rfl)
  calc ∑ j, ‖P i j‖ ^ 2 = ∑ j, ((P i j).re ^ 2 + (P i j).im ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
    _ = ∑ j, (P i j).re ^ 2 + ∑ j, (P i j).im ^ 2 := Finset.sum_add_distrib
    _ ≤ 2 * p ^ 2 := by linarith

/-- `|v| ≤ √N c` when `|v_j| ≤ c`. -/
private lemma ecw_testNorm_le (v : Fin N → ℝ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, |v j| ≤ c) :
    testNorm v ≤ Real.sqrt N * c := by
  unfold testNorm
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (Nat.cast_nonneg N)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, v j ^ 2 ≤ ∑ _j : Fin N, c ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
    _ = N * c ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `∑_j u_j B_{ij}` through the real test vectors `Re u`, `Im u`: if
`|⟨e_i, B w⟩| ≤ δ₀ |w|` for both and `|u_j| ≤ c`, then `|∑_j u_j B_{ij}| ≤ 2 δ₀ √N c`. -/
private lemma ecw_rho (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) (u : Fin N → ℂ) {δ₀ c : ℝ}
    (hδ0 : 0 ≤ δ₀) (hc : 0 ≤ c) (hu : ∀ j, ‖u j‖ ≤ c)
    (hre : ‖testBilin (Pi.single i 1) B (fun j => (u j).re)‖ ≤
      δ₀ * testNorm (fun j => (u j).re))
    (him : ‖testBilin (Pi.single i 1) B (fun j => (u j).im)‖ ≤
      δ₀ * testNorm (fun j => (u j).im)) :
    ‖∑ j, u j * B i j‖ ≤ δ₀ * (2 * (Real.sqrt N * c)) := by
  have e : ∑ j, u j * B i j = testBilin (Pi.single i 1) B (fun j => (u j).re) +
      Complex.I * testBilin (Pi.single i 1) B (fun j => (u j).im) := by
    rw [ecw_testBilin_single_left, ecw_testBilin_single_left, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (u j)]
    ring
  have h1 : testNorm (fun j => (u j).re) ≤ Real.sqrt N * c :=
    ecw_testNorm_le _ hc fun j => (Complex.abs_re_le_norm _).trans (hu j)
  have h2 : testNorm (fun j => (u j).im) ≤ Real.sqrt N * c :=
    ecw_testNorm_le _ hc fun j => (Complex.abs_im_le_norm _).trans (hu j)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  have a1 := hre.trans (mul_le_mul_of_nonneg_left h1 hδ0)
  have a2 := him.trans (mul_le_mul_of_nonneg_left h2 hδ0)
  linarith

/-- The random part of the order-three words summed against `s`: with `|G_{ab} - P_{ab}| ≤ δ₀`,
`|P_{ab}| ≤ p`, `∑_j |P_{ij}|² ≤ r₂`, and `|∑_j u_{ij} (G - P)_{ij}| ≤ ρ` for
`u_{ij} = 1(i < j) s_{ij} P_{jj}`,
`|∑_{i<j} s_{ij} P_{ij}(G) - 6 ∑_{i<j} s_{ij} P_{ij} P_{ii} P_{jj}|` is at most the sum of the
fluctuation terms. -/
private lemma ecw_Rbound (s : Fin N → Fin N → ℝ) {S : ℝ} (hs : ∀ i j, |s i j| ≤ S)
    (G P : Matrix (Fin N) (Fin N) ℂ) {p δ₀ r2 ρ : ℝ} (hS0 : 0 ≤ S) (hp : 0 ≤ p) (hδ0 : 0 ≤ δ₀)
    (hδ1 : δ₀ ≤ 1) (hGP : ∀ a b, ‖G a b - P a b‖ ≤ δ₀) (hP : ∀ a b, ‖P a b‖ ≤ p)
    (hr : ∀ i, ∑ j, ‖P i j‖ ^ 2 ≤ r2)
    (hρ : ∀ i, ‖∑ j, (if i < j then (s i j : ℂ) * P j j else 0) * (G i j - P i j)‖ ≤ ρ) :
    ‖(∑ i, ∑ j, if i < j then (s i j : ℂ) * ecwP G i j else 0) -
        6 * ∑ i, ∑ j, if i < j then (s i j : ℂ) * (P i j * (P i i * P j j)) else 0‖ ≤
      S * (4 * (p + 1) * (N * r2 + N ^ 2 * δ₀ ^ 2) +
        6 * (2 * p + 1) * δ₀ * (N * (Real.sqrt N * Real.sqrt r2) + N ^ 2 * δ₀)) +
        6 * (N * (p * ρ)) := by
  have hS : ∀ _i _j : Fin N, 0 ≤ S := fun _ _ => hS0
  have hG : ∀ a b, ‖G a b‖ ≤ ‖P a b‖ + δ₀ := fun a b => by
    have e : G a b = P a b + (G a b - P a b) := by ring
    rw [e]; exact (norm_add_le _ _).trans (add_le_add le_rfl (hGP a b))
  have hG1 : ∀ a b, ‖G a b‖ ≤ p + 1 := fun a b => (hG a b).trans (by linarith [hP a b])
  -- the decomposition
  have hdec : (∑ i, ∑ j, if i < j then (s i j : ℂ) * ecwP G i j else 0) -
      6 * (∑ i, ∑ j, if i < j then (s i j : ℂ) * (P i j * (P i i * P j j)) else 0) =
      (∑ i, ∑ j, if i < j then (s i j : ℂ) *
        (2 * G i j ^ 3 + 6 * G i j * (G i i * G j j - P i i * P j j)) else 0) +
      6 * ∑ i, P i i *
        ∑ j, (if i < j then (s i j : ℂ) * P j j else 0) * (G i j - P i j) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · simp only [ecwP]; ring
    · ring
  rw [hdec]
  -- the first part, entry by entry
  have hcij : ∀ i j, ‖if i < j then (s i j : ℂ) *
      (2 * G i j ^ 3 + 6 * G i j * (G i i * G j j - P i i * P j j)) else 0‖ ≤
        S * (4 * (p + 1) * (‖P i j‖ ^ 2 + δ₀ ^ 2) + 6 * (2 * p + 1) * δ₀ * (‖P i j‖ + δ₀)) := by
    intro i j
    split_ifs with hij
    · have hd : ‖G i i * G j j - P i i * P j j‖ ≤ (2 * p + 1) * δ₀ := by
        have e : G i i * G j j - P i i * P j j =
            (G i i - P i i) * G j j + P i i * (G j j - P j j) := by ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul (hGP i i) (hG1 j j) (norm_nonneg _) hδ0
        have := mul_le_mul (hP i i) (hGP j j) (norm_nonneg _) hp
        nlinarith
      have hg := hG i j
      have hg1 := hG1 i j
      have hg0 := norm_nonneg (G i j)
      have hpij := norm_nonneg (P i j)
      have hsq : ‖G i j‖ ^ 2 ≤ 2 * (‖P i j‖ ^ 2 + δ₀ ^ 2) := by
        nlinarith [sq_nonneg (‖P i j‖ - δ₀), mul_le_mul hg hg hg0 (by positivity)]
      have hcube : ‖G i j‖ ^ 3 ≤ (p + 1) * (2 * (‖P i j‖ ^ 2 + δ₀ ^ 2)) := by
        have : ‖G i j‖ ^ 3 = ‖G i j‖ * ‖G i j‖ ^ 2 := by ring
        rw [this]
        exact mul_le_mul hg1 hsq (by positivity) (by linarith)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (hs i j) ?_ (norm_nonneg _) (hS i j)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_pow]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 : ‖(6 : ℂ)‖ = 6 := by norm_num
      rw [h2, h6]
      have := mul_le_mul hg hd (norm_nonneg _) (by positivity)
      nlinarith
    · rw [norm_zero]
      have := hS i j
      positivity
  have hrow1 : ∀ i, ∑ j, ‖P i j‖ ≤ Real.sqrt N * Real.sqrt r2 := fun i =>
    (ecw_cs (fun j => P i j)).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hr i)) (Real.sqrt_nonneg _))
  have hpart1 : ‖∑ i, ∑ j, if i < j then (s i j : ℂ) *
      (2 * G i j ^ 3 + 6 * G i j * (G i i * G j j - P i i * P j j)) else 0‖ ≤
        S * (4 * (p + 1) * (N * r2 + N ^ 2 * δ₀ ^ 2) +
          6 * (2 * p + 1) * δ₀ * (N * (Real.sqrt N * Real.sqrt r2) + N ^ 2 * δ₀)) := by
    have hsum : ∀ (a b : Fin N → ℝ) (u v d d' : ℝ),
        ∑ j, S * (u * (a j + d) + v * (b j + d')) =
          S * (u * (∑ j, a j + N * d) + v * (∑ j, b j + N * d')) := by
      intro a b u v d d'
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc _ ≤ ∑ i, ‖∑ j, if i < j then (s i j : ℂ) *
          (2 * G i j ^ 3 + 6 * G i j * (G i i * G j j - P i i * P j j)) else 0‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖if i < j then (s i j : ℂ) *
          (2 * G i j ^ 3 + 6 * G i j * (G i i * G j j - P i i * P j j)) else 0‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, S * (4 * (p + 1) * (r2 + N * δ₀ ^ 2) +
          6 * (2 * p + 1) * δ₀ * (Real.sqrt N * Real.sqrt r2 + N * δ₀)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc _ ≤ ∑ j, S * (4 * (p + 1) * (‖P i j‖ ^ 2 + δ₀ ^ 2) +
                6 * (2 * p + 1) * δ₀ * (‖P i j‖ + δ₀)) := Finset.sum_le_sum fun j _ => hcij i j
            _ = S * (4 * (p + 1) * (∑ j, ‖P i j‖ ^ 2 + N * δ₀ ^ 2) +
                6 * (2 * p + 1) * δ₀ * (∑ j, ‖P i j‖ + N * δ₀)) := hsum _ _ _ _ _ _
            _ ≤ _ := by
                have := hr i
                have := hrow1 i
                gcongr
      _ = S * (4 * (p + 1) * (N * r2 + N ^ 2 * δ₀ ^ 2) +
          6 * (2 * p + 1) * δ₀ * (N * (Real.sqrt N * Real.sqrt r2) + N ^ 2 * δ₀)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hpart2 : ‖6 * ∑ i, P i i *
      ∑ j, (if i < j then (s i j : ℂ) * P j j else 0) * (G i j - P i j)‖ ≤
        6 * (N * (p * ρ)) := by
    rw [norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc _ ≤ ∑ i, ‖P i i *
          ∑ j, (if i < j then (s i j : ℂ) * P j j else 0) * (G i j - P i j)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, p * ρ := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]; exact mul_le_mul (hP i i) (hρ i) (norm_nonneg _) hp
      _ = N * (p * ρ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (norm_add_le _ _).trans (add_le_add hpart1 hpart2)

/-- The deterministic order-three words: the increment of `∑_{i<j} s_{ij} P_{ij} P_{ii} P_{jj}`
between the two window points is at most `S N^{3/2} (p² κ + 2 p κ √r₂)` when
`|P_{ab}|, |P'_{ab}| ≤ p`, `∑_j |P_{ij}|² ≤ r₂`, `|P'_{ab} - P_{ab}| ≤ κ` and
`∑_j |P'_{ij} - P_{ij}|² ≤ κ²`. -/
private lemma ecw_Dbound (s : Fin N → Fin N → ℝ) {S : ℝ} (hs : ∀ i j, |s i j| ≤ S)
    (Pa Pb : Matrix (Fin N) (Fin N) ℂ) {p κ r2 : ℝ} (hS0 : 0 ≤ S) (hp : 0 ≤ p) (hκ0 : 0 ≤ κ)
    (hPa : ∀ a b, ‖Pa a b‖ ≤ p) (hPb : ∀ a b, ‖Pb a b‖ ≤ p)
    (hr : ∀ i, ∑ j, ‖Pa i j‖ ^ 2 ≤ r2)
    (hκ : ∀ a b, ‖Pb a b - Pa a b‖ ≤ κ) (hκr : ∀ i, ∑ j, ‖Pb i j - Pa i j‖ ^ 2 ≤ κ ^ 2) :
    ‖(∑ i, ∑ j, if i < j then (s i j : ℂ) * (Pb i j * (Pb i i * Pb j j)) else 0) -
        ∑ i, ∑ j, if i < j then (s i j : ℂ) * (Pa i j * (Pa i i * Pa j j)) else 0‖ ≤
      S * (N * (Real.sqrt N * (p ^ 2 * κ + 2 * p * κ * Real.sqrt r2))) := by
  have hterm : ∀ i j, ‖(if i < j then (s i j : ℂ) * (Pb i j * (Pb i i * Pb j j)) else 0) -
      (if i < j then (s i j : ℂ) * (Pa i j * (Pa i i * Pa j j)) else 0)‖ ≤
        S * (p ^ 2 * ‖Pb i j - Pa i j‖ + 2 * p * κ * ‖Pa i j‖) := by
    intro i j
    split_ifs
    · have e : (s i j : ℂ) * (Pb i j * (Pb i i * Pb j j)) -
          (s i j : ℂ) * (Pa i j * (Pa i i * Pa j j)) =
          (s i j : ℂ) * ((Pb i j - Pa i j) * (Pb i i * Pb j j) +
            Pa i j * ((Pb i i - Pa i i) * Pb j j + Pa i i * (Pb j j - Pa j j))) := by ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (hs i j) ?_ (norm_nonneg _) hS0
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖Pb i i‖ * ‖Pb j j‖ ≤ p ^ 2 := by
        rw [sq]; exact mul_le_mul (hPb i i) (hPb j j) (norm_nonneg _) hp
      have h2 : ‖(Pb i i - Pa i i) * Pb j j + Pa i i * (Pb j j - Pa j j)‖ ≤ 2 * p * κ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul (hκ i i) (hPb j j) (norm_nonneg _) hκ0
        have := mul_le_mul (hPa i i) (hκ j j) (norm_nonneg _) hp
        nlinarith
      have h3 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (Pb i j - Pa i j))
      have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (Pa i j))
      nlinarith
    · rw [sub_zero, norm_zero]
      have := norm_nonneg (Pb i j - Pa i j)
      have := norm_nonneg (Pa i j)
      positivity
  have hrowΔ : ∀ i, ∑ j, ‖Pb i j - Pa i j‖ ≤ Real.sqrt N * κ := fun i => by
    refine (ecw_cs (fun j => Pb i j - Pa i j)).trans (mul_le_mul_of_nonneg_left ?_
      (Real.sqrt_nonneg _))
    calc Real.sqrt (∑ j, ‖Pb i j - Pa i j‖ ^ 2) ≤ Real.sqrt (κ ^ 2) := Real.sqrt_le_sqrt (hκr i)
      _ = κ := Real.sqrt_sq hκ0
  have hrowa : ∀ i, ∑ j, ‖Pa i j‖ ≤ Real.sqrt N * Real.sqrt r2 := fun i =>
    (ecw_cs (fun j => Pa i j)).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hr i)) (Real.sqrt_nonneg _))
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i, ‖(∑ j, if i < j then (s i j : ℂ) * (Pb i j * (Pb i i * Pb j j)) else 0) -
        ∑ j, if i < j then (s i j : ℂ) * (Pa i j * (Pa i i * Pa j j)) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, S * (Real.sqrt N * (p ^ 2 * κ + 2 * p * κ * Real.sqrt r2)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        calc _ ≤ ∑ j, ‖(if i < j then (s i j : ℂ) * (Pb i j * (Pb i i * Pb j j)) else 0) -
              (if i < j then (s i j : ℂ) * (Pa i j * (Pa i i * Pa j j)) else 0)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ j, S * (p ^ 2 * ‖Pb i j - Pa i j‖ + 2 * p * κ * ‖Pa i j‖) :=
              Finset.sum_le_sum fun j _ => hterm i j
          _ = S * (p ^ 2 * ∑ j, ‖Pb i j - Pa i j‖ + 2 * p * κ * ∑ j, ‖Pa i j‖) := by
              simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          _ ≤ S * (p ^ 2 * (Real.sqrt N * κ) + 2 * p * κ * (Real.sqrt N * Real.sqrt r2)) := by
              have := hrowΔ i
              have := hrowa i
              gcongr
          _ = S * (Real.sqrt N * (p ^ 2 * κ + 2 * p * κ * Real.sqrt r2)) := by ring
    _ = S * (N * (Real.sqrt N * (p ^ 2 * κ + 2 * p * κ * Real.sqrt r2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Sums
/-! ## The third-order sum on the good event -/

section GoodSum

variable {N : ℕ}

/-- The third-order sum at a symmetric `W` on the good event: at every window point
`|G_{ab} - Π_{ab}| ≤ δ₀`, `|Π_{ab}| ≤ p`, `∑_j |Π_{ij}|² ≤ 2p²`, the anisotropic bounds for the
test vectors `(1(i<j) s_{ij} Π_{jj})_j`, and the increments of `Π` between the two points are at
most `κ` (entries) and `κ` (rows); then `∑_{i<j} s_{ij} ∂³_{ij} F(𝒳)` is at most
`N² S · 4 l C_b Θ² + 2 l C_b (2 B_R + 6 B_D)`. -/
private lemma ecw_good_sum {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ}
    (hF : ContDiff ℝ 5 F) (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb)
    (Ea Eb : Fin l → ℝ) (s : Fin N → Fin N → ℝ) {S p δ₀ κ Θ BR BD : ℝ}
    (hs : ∀ i j, |s i j| ≤ S) (hS0 : 0 ≤ S) (hp : 0 ≤ p) (hδ0 : 0 ≤ δ₀) (hδ1 : δ₀ ≤ 1)
    (hκ0 : 0 ≤ κ) (hΘ : 480 * (2 * (p + 1)) ^ 4 * (2 * δ₀ + κ) ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hBR : S * (4 * (p + 1) * (N * (2 * p ^ 2) + N ^ 2 * δ₀ ^ 2) +
        6 * (2 * p + 1) * δ₀ * (N * (Real.sqrt N * Real.sqrt (2 * p ^ 2)) + N ^ 2 * δ₀)) +
        6 * (N * (p * (δ₀ * (2 * (Real.sqrt N * (S * p)))))) ≤ BR)
    (hBD : S * (N * (Real.sqrt N * (p ^ 2 * κ + 2 * p * κ * Real.sqrt (2 * p ^ 2)))) ≤ BD)
    (hP : ∀ k a b, ‖piW A ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ p ∧
      ‖piW A ((Eb k : ℂ) + η * Complex.I) a b‖ ≤ p)
    (hr : ∀ k i, ∑ j, ‖piW A ((Ea k : ℂ) + η * Complex.I) i j‖ ^ 2 ≤ 2 * p ^ 2 ∧
      ∑ j, ‖piW A ((Eb k : ℂ) + η * Complex.I) i j‖ ^ 2 ≤ 2 * p ^ 2)
    (hκ : ∀ k a b, ‖piW A ((Eb k : ℂ) + η * Complex.I) a b -
      piW A ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ κ)
    (hκr : ∀ k i, ∑ j, ‖piW A ((Eb k : ℂ) + η * Complex.I) i j -
      piW A ((Ea k : ℂ) + η * Complex.I) i j‖ ^ 2 ≤ κ ^ 2)
    (hGP : ∀ k a b, ‖GW A Wm ((Ea k : ℂ) + η * Complex.I) a b -
      piW A ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ δ₀ ∧
      ‖GW A Wm ((Eb k : ℂ) + η * Complex.I) a b - piW A ((Eb k : ℂ) + η * Complex.I) a b‖ ≤ δ₀)
    (hρ : ∀ k i, ‖∑ j, (if i < j then (s i j : ℂ) * piW A ((Ea k : ℂ) + η * Complex.I) j j
        else 0) * (GW A Wm ((Ea k : ℂ) + η * Complex.I) i j -
          piW A ((Ea k : ℂ) + η * Complex.I) i j)‖ ≤ δ₀ * (2 * (Real.sqrt N * (S * p))) ∧
      ‖∑ j, (if i < j then (s i j : ℂ) * piW A ((Eb k : ℂ) + η * Complex.I) j j
        else 0) * (GW A Wm ((Eb k : ℂ) + η * Complex.I) i j -
          piW A ((Eb k : ℂ) + η * Complex.I) i j)‖ ≤ δ₀ * (2 * (Real.sqrt N * (S * p)))) :
    |∑ i, ∑ j, if i < j then s i j * smTW 3 F A Wm η Ea Eb i j (Wm i j) else 0| ≤
      N ^ 2 * (S * (l * (Cb * (4 * Θ ^ 2)))) + l * (Cb * (2 * (2 * BR + 6 * BD))) := by
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  set za : Fin l → ℂ := fun k => (Ea k : ℂ) + η * Complex.I with hza
  set zb : Fin l → ℂ := fun k => (Eb k : ℂ) + η * Complex.I with hzb
  set c : Fin l → ℝ := fun k =>
    fderiv ℝ F (fun k' => smCount (Wm + A) η (Ea k') (Eb k')) (Pi.single k 1) with hc
  have hc0 : ∀ k, |c k| ≤ Cb := fun k => by
    have h := ecw_partial_bound hF hFb k 0 (by norm_num)
      (fun k' => smCount (Wm + A) η (Ea k') (Eb k'))
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  set f : Fin l → Fin N → Fin N → ℝ := fun k i j =>
    -(1 / Real.pi) * (2 * ((ecwP (GW A Wm (zb k)) i j).im - (ecwP (GW A Wm (za k)) i j).im))
    with hf
  set Q : Matrix (Fin N) (Fin N) ℂ → ℂ := fun B =>
    ∑ i, ∑ j, if i < j then (s i j : ℂ) * ecwP B i j else 0 with hQ
  set D : Matrix (Fin N) (Fin N) ℂ → ℂ := fun B =>
    ∑ i, ∑ j, if i < j then (s i j : ℂ) * (B i j * (B i i * B j j)) else 0 with hD
  have hΘ0 : 0 ≤ Θ := le_trans (by positivity) hΘ
  -- one entry
  have hent : ∀ i j, i < j →
      |smTW 3 F A Wm η Ea Eb i j (Wm i j) - ∑ k, c k * f k i j| ≤ l * (Cb * (4 * Θ ^ 2)) := by
    intro i j hij
    have hG : ∀ (z : ℂ) (a b : Fin N), ‖GW A Wm z a b - piW A z a b‖ ≤ δ₀ →
        ‖piW A z a b‖ ≤ p → ‖GW A Wm z a b‖ ≤ p + 1 := by
      intro z a b h1 h2
      have e : GW A Wm z a b = piW A z a b + (GW A Wm z a b - piW A z a b) := by ring
      rw [e]
      exact (norm_add_le _ _).trans (by linarith)
    refine ecw_entry hA hW hη hF hFb Ea Eb hij.ne (Wb := p + 1) (δ := 2 * δ₀ + κ)
      (by linarith) (by positivity) (fun k a _ b _ => hG _ a b (hGP k a b).1 (hP k a b).1)
      (fun k a _ b _ => hG _ a b (hGP k a b).2 (hP k a b).2) (fun k a _ b _ => ?_) hΘ hΘ1
    have e : GW A Wm (zb k) a b - GW A Wm (za k) a b =
        (GW A Wm (zb k) a b - piW A (zb k) a b) + (piW A (zb k) a b - piW A (za k) a b) -
          (GW A Wm (za k) a b - piW A (za k) a b) := by ring
    change ‖GW A Wm (zb k) a b - GW A Wm (za k) a b‖ ≤ 2 * δ₀ + κ
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := norm_add_le (GW A Wm (zb k) a b - piW A (zb k) a b)
      (piW A (zb k) a b - piW A (za k) a b)
    linarith [(hGP k a b).1, (hGP k a b).2, hκ k a b]
  -- the leading terms
  have hIm : ∀ B, (Q B).im = ∑ i, ∑ j, if i < j then s i j * (ecwP B i j).im else 0 := by
    intro B
    simp only [hQ, Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hlead : (∑ i, ∑ j, if i < j then s i j * ∑ k, c k * f k i j else 0) =
      ∑ k, c k * (-(1 / Real.pi) * (2 * ((Q (GW A Wm (zb k))).im - (Q (GW A Wm (za k))).im))) := by
    calc (∑ i, ∑ j, if i < j then s i j * ∑ k, c k * f k i j else 0) =
        ∑ i, ∑ j, ∑ k, c k * (if i < j then s i j * f k i j else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          split_ifs
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
          · simp
      _ = ∑ k, ∑ i, ∑ j, c k * (if i < j then s i j * f k i j else 0) := by
          refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hIm, hIm]
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [hf]
          split_ifs <;> ring
  -- the bounds on `Q`
  have hQb : ∀ k, ‖Q (GW A Wm (zb k)) - Q (GW A Wm (za k))‖ ≤ 2 * BR + 6 * BD := by
    intro k
    have hRb := ecw_Rbound s hs (GW A Wm (zb k)) (piW A (zb k)) hS0 hp hδ0 hδ1
      (fun a b => (hGP k a b).2) (fun a b => (hP k a b).2) (fun i => (hr k i).2)
      (fun i => (hρ k i).2)
    have hRa := ecw_Rbound s hs (GW A Wm (za k)) (piW A (za k)) hS0 hp hδ0 hδ1
      (fun a b => (hGP k a b).1) (fun a b => (hP k a b).1) (fun i => (hr k i).1)
      (fun i => (hρ k i).1)
    have hDD := ecw_Dbound s hs (piW A (za k)) (piW A (zb k)) hS0 hp hκ0
      (fun a b => (hP k a b).1) (fun a b => (hP k a b).2) (fun i => (hr k i).1) (hκ k)
      (hκr k)
    have e : Q (GW A Wm (zb k)) - Q (GW A Wm (za k)) =
        (Q (GW A Wm (zb k)) - 6 * D (piW A (zb k))) + 6 * (D (piW A (zb k)) - D (piW A (za k))) -
          (Q (GW A Wm (za k)) - 6 * D (piW A (za k))) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num]
    have h1 : ‖Q (GW A Wm (zb k)) - 6 * D (piW A (zb k))‖ ≤ BR := hRb.trans hBR
    have h2 : ‖Q (GW A Wm (za k)) - 6 * D (piW A (za k))‖ ≤ BR := hRa.trans hBR
    have h3 : ‖D (piW A (zb k)) - D (piW A (za k))‖ ≤ BD := hDD.trans hBD
    linarith
  have hmain : |∑ k, c k * (-(1 / Real.pi) *
      (2 * ((Q (GW A Wm (zb k))).im - (Q (GW A Wm (za k))).im)))| ≤
        l * (Cb * (2 * (2 * BR + 6 * BD))) := by
    have hpi : 1 / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |c k * (-(1 / Real.pi) *
          (2 * ((Q (GW A Wm (zb k))).im - (Q (GW A Wm (za k))).im)))| ≤
        ∑ _k : Fin l, Cb * (2 * (2 * BR + 6 * BD)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hc0 k) ?_ (abs_nonneg _) hCb
          have hd : |(Q (GW A Wm (zb k))).im - (Q (GW A Wm (za k))).im| ≤ 2 * BR + 6 * BD := by
            rw [← Complex.sub_im]
            exact (Complex.abs_im_le_norm _).trans (hQb k)
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), abs_mul,
            abs_two]
          calc 1 / Real.pi * (2 * |(Q (GW A Wm (zb k))).im - (Q (GW A Wm (za k))).im|) ≤
              1 * (2 * (2 * BR + 6 * BD)) := by gcongr
            _ = 2 * (2 * BR + 6 * BD) := one_mul _
      _ = l * (Cb * (2 * (2 * BR + 6 * BD))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the assembly
  have hsplit : (∑ i, ∑ j, if i < j then s i j * smTW 3 F A Wm η Ea Eb i j (Wm i j) else 0) =
      (∑ i, ∑ j, if i < j then s i j *
        (smTW 3 F A Wm η Ea Eb i j (Wm i j) - ∑ k, c k * f k i j) else 0) +
      ∑ i, ∑ j, if i < j then s i j * ∑ k, c k * f k i j else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hrest : |∑ i, ∑ j, if i < j then s i j *
      (smTW 3 F A Wm η Ea Eb i j (Wm i j) - ∑ k, c k * f k i j) else 0| ≤
        N ^ 2 * (S * (l * (Cb * (4 * Θ ^ 2)))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, if i < j then s i j *
          (smTW 3 F A Wm η Ea Eb i j (Wm i j) - ∑ k, c k * f k i j) else 0| ≤
        ∑ _i : Fin N, ∑ _j : Fin N, S * (l * (Cb * (4 * Θ ^ 2))) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs with hij
          · rw [abs_mul]
            exact mul_le_mul (hs i j) (hent i j hij) (abs_nonneg _) hS0
          · rw [abs_zero]; positivity
      _ = N ^ 2 * (S * (l * (Cb * (4 * Θ ^ 2)))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add hrest ?_)
  rw [hlead]
  exact hmain

end GoodSum
/-! ## The exponent bookkeeping of the third-order sum -/

section ThirdArith

/-- The powers of `N` met in the third-order sum are at most `N^{4/3+22ε}`. -/
private lemma ecw_pow_facts {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    (N : ℝ) * (Real.sqrt N * (N : ℝ) ^ (-1 / 3 + 10 * ε)) ≤ (N : ℝ) ^ (4 / 3 + 22 * ε) ∧
    (N : ℝ) ^ 2 * ((N : ℝ) ^ (-1 / 3 + 10 * ε)) ^ 2 ≤ (N : ℝ) ^ (4 / 3 + 22 * ε) ∧
    (N : ℝ) ≤ (N : ℝ) ^ (4 / 3 + 22 * ε) ∧
    (N : ℝ) * (Real.sqrt N * (N : ℝ) ^ (-1 / 3 + 21 * ε / 2)) ≤ (N : ℝ) ^ (4 / 3 + 22 * ε) ∧
    (N : ℝ) ^ 2 * ((N : ℝ) ^ (-1 / 3 + 11 * ε)) ^ 2 ≤ (N : ℝ) ^ (4 / 3 + 22 * ε) ∧
    (N : ℝ) ^ 4 * ((N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 3 * (N : ℝ) ^ (-(10 : ℝ)) ≤
      (N : ℝ) ^ (4 / 3 + 22 * ε) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hpow : ∀ (a : ℝ) (k : ℕ), ((N : ℝ) ^ a) ^ k = (N : ℝ) ^ (a * k) := fun a k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have hnat : ∀ k : ℕ, (N : ℝ) ^ k = (N : ℝ) ^ (k : ℝ) := fun k => (Real.rpow_natCast _ k).symm
  have hone : ∀ b : ℝ, (N : ℝ) * (N : ℝ) ^ b = (N : ℝ) ^ (1 + b) := fun b => by
    rw [Real.rpow_add hn, Real.rpow_one]
  have hsq : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hle : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hn1 h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsq, ← Real.rpow_add hn, hone]
    exact hle _ _ (by linarith)
  · rw [hpow, hnat, ← Real.rpow_add hn]
    exact hle _ _ (by push_cast; linarith)
  · calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := hle _ _ (by linarith)
  · rw [hsq, ← Real.rpow_add hn, hone]
    exact hle _ _ (by linarith)
  · rw [hpow, hnat, ← Real.rpow_add hn]
    exact hle _ _ (by push_cast; linarith)
  · rw [hpow, hnat, ← Real.rpow_add hn, ← Real.rpow_add hn]
    exact hle _ _ (by push_cast; linarith)

/-- The fluctuation constant of the third-order sum. -/
private lemma ecw_arith_BR {S p cψ u δ₀ X n sn : ℝ} (hS0 : 0 ≤ S) (hp0 : 0 ≤ p) (hcψ : 0 ≤ cψ)
    (hδ₀ : δ₀ = cψ * u) (f1 : n * (sn * u) ≤ X) (f2 : n ^ 2 * u ^ 2 ≤ X) (f3 : n ≤ X) :
    S * (4 * (p + 1) * (n * (2 * p ^ 2) + n ^ 2 * δ₀ ^ 2) +
      6 * (2 * p + 1) * δ₀ * (n * (sn * Real.sqrt (2 * p ^ 2)) + n ^ 2 * δ₀)) +
      6 * (n * (p * (δ₀ * (2 * (sn * (S * p)))))) ≤
    S * (4 * (p + 1) * (2 * p ^ 2 + cψ ^ 2) +
      6 * (2 * p + 1) * (cψ * Real.sqrt (2 * p ^ 2) + cψ ^ 2) + 12 * p ^ 2 * cψ) * X := by
  have e : S * (4 * (p + 1) * (n * (2 * p ^ 2) + n ^ 2 * δ₀ ^ 2) +
      6 * (2 * p + 1) * δ₀ * (n * (sn * Real.sqrt (2 * p ^ 2)) + n ^ 2 * δ₀)) +
      6 * (n * (p * (δ₀ * (2 * (sn * (S * p)))))) =
      S * (4 * (p + 1) * (2 * p ^ 2 * n + cψ ^ 2 * (n ^ 2 * u ^ 2)) +
        6 * (2 * p + 1) * (cψ * Real.sqrt (2 * p ^ 2) * (n * (sn * u)) +
          cψ ^ 2 * (n ^ 2 * u ^ 2))) + 12 * p ^ 2 * cψ * S * (n * (sn * u)) := by
    rw [hδ₀]; ring
  rw [e]
  calc _ ≤ S * (4 * (p + 1) * (2 * p ^ 2 * X + cψ ^ 2 * X) +
        6 * (2 * p + 1) * (cψ * Real.sqrt (2 * p ^ 2) * X + cψ ^ 2 * X)) +
        12 * p ^ 2 * cψ * S * X := by gcongr
    _ = _ := by ring

/-- The deterministic constant of the third-order sum. -/
private lemma ecw_arith_BD {S p Kp v κ X n sn : ℝ} (hS0 : 0 ≤ S) (hp0 : 0 ≤ p) (hKp : 0 ≤ Kp)
    (hκ : κ = Kp * v) (f4 : n * (sn * v) ≤ X) :
    S * (n * (sn * (p ^ 2 * κ + 2 * p * κ * Real.sqrt (2 * p ^ 2)))) ≤
      S * (p ^ 2 * Kp + 2 * p * Kp * Real.sqrt (2 * p ^ 2)) * X := by
  have e : S * (n * (sn * (p ^ 2 * κ + 2 * p * κ * Real.sqrt (2 * p ^ 2)))) =
      S * (p ^ 2 * Kp + 2 * p * Kp * Real.sqrt (2 * p ^ 2)) * (n * (sn * v)) := by
    rw [hκ]; ring
  rw [e]
  gcongr

/-- The final bookkeeping of the third-order sum. -/
private lemma ecw_arith_final {S Cb l cΘ cR cD w X n Θ Bg Bc Bc1 E10 ET q : ℝ} (hS0 : 0 ≤ S)
    (hCb : 0 ≤ Cb) (hl : 0 ≤ l) (hq0 : 0 ≤ q)
    (hΘ : Θ = cΘ * w) (f5 : n ^ 2 * w ^ 2 ≤ X) (hq : n ^ 4 * q * E10 ≤ X)
    (hBg : Bg = n ^ 2 * (S * (l * (Cb * (4 * Θ ^ 2)))) +
      l * (Cb * (2 * (2 * (S * cR * X) + 6 * (S * cD * X)))))
    (hBc1 : Bc1 = 6 * Cb * (192 ^ 3 * q)) (hBc : Bc = n ^ 2 * (S * Bc1))
    (hET : ET ≤ 6 * l * n ^ 2 * E10) :
    Bg + Bc * ET ≤
      (4 * l * cΘ ^ 2 + 2 * l * (2 * cR + 6 * cD) + 36 * 192 ^ 3 * l) * S * Cb * X := by
  have hBc0 : 0 ≤ Bc := by rw [hBc, hBc1]; positivity
  have h1 : Bc * ET ≤ 36 * 192 ^ 3 * l * S * Cb * (n ^ 4 * q * E10) := by
    calc Bc * ET ≤ Bc * (6 * l * n ^ 2 * E10) := mul_le_mul_of_nonneg_left hET hBc0
      _ = _ := by rw [hBc, hBc1]; ring
  have h2 : 36 * 192 ^ 3 * l * S * Cb * (n ^ 4 * q * E10) ≤ 36 * 192 ^ 3 * l * S * Cb * X := by
    gcongr
  have h3 : Bg = 4 * l * cΘ ^ 2 * S * Cb * (n ^ 2 * w ^ 2) +
      2 * l * (2 * cR + 6 * cD) * S * Cb * X := by
    rw [hBg, hΘ]; ring
  have h4 : 4 * l * cΘ ^ 2 * S * Cb * (n ^ 2 * w ^ 2) ≤ 4 * l * cΘ ^ 2 * S * Cb * X := by
    gcongr
  rw [h3]
  linarith

/-- The number of events of the third-order sum is at most `6 l N²`. -/
private lemma ecw_card_le {N : ℕ} (hN : 1 ≤ N) (l : ℕ) :
    (Fintype.card (Fin l × Bool × ((Fin N × Fin N) ⊕ (Fin N × Bool))) : ℝ) ≤
      6 * l * (N : ℝ) ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
  push_cast
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (N : ℝ) * N + N * 2 ≤ 3 * (N : ℝ) ^ 2 := by nlinarith
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  nlinarith

end ThirdArith
/-! ## The third-order sum

The order-three term of the Green function comparison near the edge in the proof of
Theorem 12.5, on the comparison window `|E − L₊| ≤ 3N^{-2/3+ε}`, `η = N^{-2/3-9ε}`, for a
deterministic array `s_{ij}`. -/

/-- The third-order sum over the off-diagonal entries:
`|∑_{i<j} s_{ij} E ∂³_{ij} F(𝒳)| ≤ K S C_b N^{4/3+22ε}` for deterministic `|s_{ij}| ≤ S`
(anisotropic law with the test vectors `(s_{ij} Π_{jj})_j`, and `|Π(z_b) - Π(z_a)|`
through `|m^W'| ≤ Im m^W / η`). -/
theorem smTW_third_sum (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ)
      (s : Fin N → Fin N → ℝ) (S : ℝ) (F : (Fin l → ℝ) → ℝ) (Cb : ℝ) (Ea Eb : Fin l → ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      (∀ i j, |s i j| ≤ S) →
      ContDiff ℝ 5 F → (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
      (∀ k, |Ea k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) ∧
        |Eb k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) →
      |∑ i, ∑ j, if i < j then
          s i j * (∫ ω, smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j)) else 0| ≤
        K * S * Cb * (N : ℝ) ^ (4 / 3 + 22 * ε) := by
  obtain ⟨ε₁, D₁, hε₁, N₁, hlaw⟩ := anisoLawW_edgeWinW τ C ε ε 10 hτ hε hε1 hε
  obtain ⟨cψ, Kp, hcψ, hKp, N₂, hN₂1, hwin⟩ := ecw_window hτ hτ4 hε hε1
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = τ⁻¹ := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hpdef]; exact hτi.le
  obtain ⟨cΘ, hcΘ⟩ : ∃ cΘ : ℝ, cΘ = 480 * (2 * (p + 1)) ^ 4 * (2 * cψ + Kp) := ⟨_, rfl⟩
  obtain ⟨cR, hcR⟩ : ∃ cR : ℝ, cR = 4 * (p + 1) * (2 * p ^ 2 + cψ ^ 2) +
      6 * (2 * p + 1) * (cψ * Real.sqrt (2 * p ^ 2) + cψ ^ 2) + 12 * p ^ 2 * cψ := ⟨_, rfl⟩
  obtain ⟨cD, hcD⟩ : ∃ cD : ℝ, cD = p ^ 2 * Kp + 2 * p * Kp * Real.sqrt (2 * p ^ 2) :=
    ⟨_, rfl⟩
  have hcΘ0 : 0 ≤ cΘ := by rw [hcΘ]; positivity
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  have hcD0 : 0 ≤ cD := by rw [hcD]; positivity
  have y1 : -1 / 3 + 10 * ε < 0 := by linarith
  have y3 : -1 / 3 + 11 * ε < 0 := by linarith
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 ((ecw_ev_small y1 (2 * cψ)).and
    (ecw_ev_small y3 (2 * cΘ)))
  refine ⟨ε₁, D₁, hε₁, 4 * l * cΘ ^ 2 + 2 * l * (2 * cR + 6 * cD) + 36 * 192 ^ 3 * l,
    max (max N₁ N₂) (max N₃ 1), ?_⟩
  intro N hN Ω _ _ A W s S F Cb Ea Eb hA hnA hW hSB hlawG hs hF hFb hwinE
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3' : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hc1, hc3⟩ := hN₃ N hN3'
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN
  have hn : (0 : ℝ) < N := by linarith
  have hη : 0 < etaE N ε := by unfold etaE; positivity
  have hlawW := hlaw N hN1' A W hA hnA hW hSB hlawG
  obtain ⟨hwinA, hpiA⟩ := hwin N hN2' A hA hnA hSB
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hs ⟨0, hNN⟩ ⟨0, hNN⟩)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hWm : Measurable W := Measurable.of_eval_matrix W fun a b => hW.measurable a b
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ecw_pow_facts hNN hε hε1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (N : ℝ) ^ (4 / 3 + 22 * ε) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (N : ℝ) ^ (-1 / 3 + 10 * ε) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (N : ℝ) ^ (-1 / 3 + 21 * ε / 2) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (N : ℝ) ^ (-1 / 3 + 11 * ε) := ⟨_, rfl⟩
  rw [← hu, ← hX] at f1 f2
  rw [← hX] at f3
  rw [← hv, ← hX] at f4
  rw [← hw, ← hX] at f5
  rw [← hX] at f6
  rw [← hu] at hc1
  rw [← hw] at hc3
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = cψ * u := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Kp * v := ⟨_, rfl⟩
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : ℝ, Θ = cΘ * w := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ₀ := by rw [hδ₀]; positivity
  have hδ1 : δ₀ ≤ 1 := by rw [hδ₀]; linarith
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hΘ1 : Θ ≤ 1 := by rw [hΘdef]; linarith
  have hΘ : 480 * (2 * (p + 1)) ^ 4 * (2 * δ₀ + κ) ≤ Θ := by
    have h10 : u ≤ w := by rw [hu, hw]; exact ecw_rpow_le hNN (by linarith)
    have h21 : v ≤ w := by rw [hv, hw]; exact ecw_rpow_le hNN (by linarith)
    rw [hΘdef, hcΘ, hδ₀, hκdef, mul_assoc (480 * (2 * (p + 1)) ^ 4)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h10 hcψ, mul_le_mul_of_nonneg_left h21 hKp]
  -- the window
  have hwz : ∀ E : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (E : ℂ) + (etaE N ε : ℝ) * Complex.I ∈ edgeWinW τ N (specOf A) ε ∧
        (N : ℝ) ^ ε * PsiW (specOf A) ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) ≤ δ₀ := by
    intro E hE'
    have h := hwinA E hE'
    refine ⟨h.1, ?_⟩
    have e : (N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε) = u := by
      rw [hu, ← Real.rpow_add hn]; congr 1; ring
    calc (N : ℝ) ^ ε * PsiW (specOf A) ((E : ℂ) + (etaE N ε : ℝ) * Complex.I)
        ≤ (N : ℝ) ^ ε * (cψ * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by gcongr; exact h.2
      _ = δ₀ := by rw [hδ₀, ← e]; ring
  have hPi : ∀ E : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) → ∀ a b : Fin N,
      ‖piW A ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ p := by
    intro E hE' a b
    have h := norm_piW_le hτ hA hSB (hwz E hE').1.1 (Pi.single a 1) (Pi.single b 1)
    rwa [ecw_testBilin_single, ecw_testNorm_single, ecw_testNorm_single, mul_one,
      mul_one, ← hpdef] at h
  have hProw : ∀ E : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) → ∀ i : Fin N,
      ∑ j, ‖piW A ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) i j‖ ^ 2 ≤ 2 * p ^ 2 := by
    intro E hE' i
    refine ecw_row_pi hp0 (fun v w => ?_) i
    rw [hpdef]
    exact norm_piW_le hτ hA hSB (hwz E hE').1.1 v w
  have hκe : ∀ k a b, ‖piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b -
      piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ κ := by
    intro k a b
    have h := (ecw_entry_le_norm (piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) -
      piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I)) a b).trans
      (hpiA (Ea k) (Eb k) (hwinE k).1 (hwinE k).2)
    rw [hκdef, hv]
    rwa [Matrix.sub_apply] at h
  have hκr : ∀ k i, ∑ j, ‖piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) i j -
      piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I) i j‖ ^ 2 ≤ κ ^ 2 := by
    intro k i
    have h := ecw_row_op (piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) -
      piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I)) i
    simp only [Matrix.sub_apply] at h
    rw [hκdef, hv]
    exact h.trans (pow_le_pow_left₀ (norm_nonneg _)
      (hpiA (Ea k) (Eb k) (hwinE k).1 (hwinE k).2) 2)
  -- the third derivatives as functions of `ω`
  have hT3e : ∀ ω i j, smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j) =
      iteratedDeriv 3 (ecwf F A (etaE N ε) Ea Eb i j (W ω)) (W ω i j) := by
    intro ω i j
    have e : ecwf F A (etaE N ε) Ea Eb i j (W ω) =
        fun t => smFW F A (Wupd (W ω) i j t) (etaE N ε) Ea Eb :=
      funext fun t => by simp only [ecwf, ecw_sym_eq (hW.symm ω)]
    rw [e]
    rfl
  have hT3m : ∀ i j, Measurable fun ω => smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j) := by
    intro i j
    have h := (ecw_measurable_iteratedDeriv (fun Wm => ecwf F A (etaE N ε) Ea Eb i j Wm)
      (ecw_f_continuous hF hA hη Ea Eb i j).measurable 5
      (fun Wm => ecw_f_contDiff hF hA hη Ea Eb i j Wm) 3 (by norm_num)).comp
      (hWm.prodMk (hW.measurable i j))
    simp_rw [hT3e]
    exact h
  obtain ⟨Bc1, hBc1⟩ : ∃ Bc1 : ℝ, Bc1 = 6 * Cb * (192 * (1 / etaE N ε)) ^ 3 := ⟨_, rfl⟩
  have hT3b : ∀ ω i j, |smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j)| ≤ Bc1 := by
    intro ω i j
    rw [hT3e]
    have h := ecw_crude hF hFb hA hη Ea Eb i j (W ω) (W ω i j) (n := 3) (by norm_num)
    have e : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [e] at h
    rw [hBc1]
    exact h
  have hBc10 : 0 ≤ Bc1 := by rw [hBc1]; positivity
  have hT3i : ∀ i j, Integrable fun ω => smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j) :=
    fun i j => Integrable.of_bound (hT3m i j).aestronglyMeasurable Bc1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hT3b ω i j)
  set Y : Ω → ℝ := fun ω => ∑ i, ∑ j, if i < j then
    s i j * smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j) else 0 with hYdef
  have hYterm : ∀ i j, Integrable fun ω => if i < j then
      s i j * smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j) else 0 := by
    intro i j
    split_ifs
    · exact (hT3i i j).const_mul _
    · exact integrable_zero _ _ _
  have hYi : Integrable Y :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hYterm i j
  have hint : (∑ i, ∑ j, if i < j then
      s i j * (∫ ω, smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j)) else 0) = ∫ ω, Y ω := by
    rw [hYdef, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hYterm i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hYterm i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [integral_const_mul]
    · simp
  have hYc : ∀ ω, |Y ω| ≤ N ^ 2 * (S * Bc1) := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, if i < j then s i j * smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j)
          else 0| ≤ ∑ _i : Fin N, ∑ _j : Fin N, S * Bc1 := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · rw [abs_mul]; exact mul_le_mul (hs i j) (hT3b ω i j) (abs_nonneg _) hS0
          · rw [abs_zero]; positivity
      _ = N ^ 2 * (S * Bc1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the events
  set zz : Fin l → Bool → ℂ := fun k b =>
    if b then (Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I else (Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I
    with hzz
  have hzzw : ∀ k b, zz k b ∈ edgeWinW τ N (specOf A) ε ∧
      (N : ℝ) ^ ε * PsiW (specOf A) (zz k b) ≤ δ₀ := by
    intro k b
    cases b
    · exact hwz _ (hwinE k).2
    · exact hwz _ (hwinE k).1
  set uv : ℂ → Fin N → Fin N → ℂ := fun z i t =>
    if i < t then (s i t : ℂ) * piW A z t t else 0 with huv
  set wv : ℂ → Fin N → Bool → Fin N → ℝ := fun z i r t =>
    if r then (uv z i t).re else (uv z i t).im with hwv
  set P : Fin l × Bool × ((Fin N × Fin N) ⊕ (Fin N × Bool)) → Set Ω := fun x =>
    Sum.elim (fun ab : Fin N × Fin N => {ω | ‖GW A (W ω) (zz x.1 x.2.1) ab.1 ab.2 -
        piW A (zz x.1 x.2.1) ab.1 ab.2‖ ≤ δ₀})
      (fun ir : Fin N × Bool => {ω | ‖testBilin (Pi.single ir.1 1)
        (GW A (W ω) (zz x.1 x.2.1) - piW A (zz x.1 x.2.1)) (wv (zz x.1 x.2.1) ir.1 ir.2)‖ ≤
          δ₀ * testNorm (wv (zz x.1 x.2.1) ir.1 ir.2)}) x.2.2 with hPdef
  have hPc : ∀ x, (ℙ : Measure Ω) (P x)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) := by
    rintro ⟨k, b, ⟨a, c⟩ | ⟨i, r⟩⟩
    · have hd := hlawW (zz k b) (hzzw k b).1 (Pi.single a 1) (Pi.single c 1)
      refine le_trans (measure_mono ?_) hd
      intro ω hω
      simp only [hPdef, Sum.elim_inl, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      simp only [Set.mem_ofPred_eq, ecw_testBilin_single, ecw_testNorm_single, Matrix.sub_apply]
      linarith [(hzzw k b).2]
    · have hd := hlawW (zz k b) (hzzw k b).1 (Pi.single i 1) (wv (zz k b) i r)
      refine le_trans (measure_mono ?_) hd
      intro ω hω
      simp only [hPdef, Sum.elim_inr, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      simp only [Set.mem_ofPred_eq, ecw_testNorm_single, mul_one]
      have h0 : 0 ≤ testNorm (wv (zz k b) i r) := Real.sqrt_nonneg _
      have h1 := mul_le_mul_of_nonneg_right (hzzw k b).2 h0
      rw [← mul_assoc]
      exact lt_of_le_of_lt h1 hω
  obtain ⟨T, hT0, hTi, hTint, hT1⟩ := ecw_events P (Real.rpow_nonneg hn.le _) hPc
  -- the bounds on the good event
  have hPz : ∀ k b, ∀ a c : Fin N, ‖piW A (zz k b) a c‖ ≤ p := by
    intro k b
    cases b
    · exact hPi _ (hwinE k).2
    · exact hPi _ (hwinE k).1
  have hBR : S * (4 * (p + 1) * (N * (2 * p ^ 2) + N ^ 2 * δ₀ ^ 2) +
      6 * (2 * p + 1) * δ₀ * (N * (Real.sqrt N * Real.sqrt (2 * p ^ 2)) + N ^ 2 * δ₀)) +
      6 * (N * (p * (δ₀ * (2 * (Real.sqrt N * (S * p)))))) ≤ S * cR * X := by
    rw [hcR]; exact ecw_arith_BR hS0 hp0 hcψ hδ₀ f1 f2 f3
  have hBD : S * (N * (Real.sqrt N * (p ^ 2 * κ + 2 * p * κ * Real.sqrt (2 * p ^ 2)))) ≤
      S * cD * X := by
    rw [hcD]; exact ecw_arith_BD hS0 hp0 hKp hκdef f4
  obtain ⟨Bg, hBg⟩ : ∃ Bg : ℝ, Bg = N ^ 2 * (S * (l * (Cb * (4 * Θ ^ 2)))) +
    l * (Cb * (2 * (2 * (S * cR * X) + 6 * (S * cD * X)))) := ⟨_, rfl⟩
  have hgood : ∀ ω, (∀ x, ω ∈ P x) → |Y ω| ≤ Bg := by
    intro ω h
    have hWh : (W ω).IsHermitian := ecw_herm_of_symm (hW.symm ω)
    have hu' : ∀ k b i t, ‖uv (zz k b) i t‖ ≤ S * p := by
      intro k b i t
      simp only [huv]
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hs i t) (hPz k b t t) (norm_nonneg _) hS0
      · rw [norm_zero]; exact mul_nonneg hS0 hp0
    have hρz : ∀ k b i, ‖∑ j, (if i < j then (s i j : ℂ) * piW A (zz k b) j j else 0) *
        (GW A (W ω) (zz k b) i j - piW A (zz k b) i j)‖ ≤ δ₀ * (2 * (Real.sqrt N * (S * p))) :=
      fun k b i => ecw_rho (GW A (W ω) (zz k b) - piW A (zz k b)) i (uv (zz k b) i) hδ0
        (mul_nonneg hS0 hp0) (hu' k b i) (h ⟨k, b, Sum.inr (i, true)⟩)
        (h ⟨k, b, Sum.inr (i, false)⟩)
    rw [hBg]
    exact ecw_good_sum hA hWh hη hF hFb Ea Eb s hs hS0 hp0 hδ0 hδ1 hκ0 hΘ hΘ1 hBR hBD
      (fun k a b => ⟨hPi _ (hwinE k).1 a b, hPi _ (hwinE k).2 a b⟩)
      (fun k i => ⟨hProw _ (hwinE k).1 i, hProw _ (hwinE k).2 i⟩) hκe hκr
      (fun k a b => ⟨h ⟨k, true, Sum.inl (a, b)⟩, h ⟨k, false, Sum.inl (a, b)⟩⟩)
      (fun k i => ⟨hρz k true i, hρz k false i⟩)
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = N ^ 2 * (S * Bc1) := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by rw [hBc]; exact mul_nonneg (sq_nonneg _) (mul_nonneg hS0 hBc10)
  have hBg0 : 0 ≤ Bg := by
    rw [hBg]
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    refine add_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hS0 (mul_nonneg hl0
      (mul_nonneg hCb (mul_nonneg (by norm_num) (sq_nonneg _)))))) (mul_nonneg hl0
      (mul_nonneg hCb (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg hS0 hcR0) hX0)) (mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg hS0 hcD0) hX0))))))
  have hpt : ∀ ω, |Y ω| ≤ Bg + Bc * T ω := by
    intro ω
    rcases hT1 ω with h | h
    · have := mul_nonneg hBc0 (hT0 ω)
      linarith [hgood ω h]
    · have h1 := mul_le_mul_of_nonneg_left h hBc0
      have h2 := hYc ω
      rw [← hBc] at h2
      linarith
  -- the expectation
  have hgi : Integrable fun ω => Bg + Bc * T ω := (integrable_const Bg).add (hTi.const_mul Bc)
  have hE : |∫ ω, Y ω| ≤ Bg + Bc * ∫ ω, T ω := by
    have h := norm_integral_le_of_norm_le hgi (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hpt ω)
    rw [Real.norm_eq_abs, integral_add (integrable_const Bg) (hTi.const_mul Bc),
      integral_const, integral_const_mul, probReal_univ, one_smul] at h
    exact h
  rw [hint, ← hX]
  refine hE.trans ?_
  have hcard := ecw_card_le hNN l
  have hηinv : 1 / etaE N ε = (N : ℝ) ^ (2 / 3 + 9 * ε) := by
    rw [etaE, one_div, ← Real.rpow_neg hn.le]
    congr 1; ring
  have hcardN : (Fintype.card (Fin l × Bool × ((Fin N × Fin N) ⊕ (Fin N × Bool))) : ℝ) *
      (N : ℝ) ^ (-(10 : ℝ)) ≤ 6 * l * (N : ℝ) ^ 2 * (N : ℝ) ^ (-(10 : ℝ)) :=
    mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hn.le _)
  rw [hηinv] at hBc1
  exact ecw_arith_final hS0 hCb (Nat.cast_nonneg l) (pow_nonneg (Real.rpow_nonneg hn.le _) 3)
    hΘdef f5 f6 hBg (by rw [hBc1]; ring) hBc (hTint.trans hcardN)
/-! ## The laws of the entries and the sample space of the swaps -/

section Laws

/-- The moment, mean and variance conditions of the class for one law on `ℝ`. -/
private structure EcwULaw (N : ℕ) (C : ℕ → ℝ) (lo hi : ℝ) (ν : Measure ℝ) : Prop where
  integrable : ∀ p : ℕ, Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν
  mean : ∫ x, x ∂ν = 0
  var_ge : lo ≤ ∫ x, x ^ 2 ∂ν
  var_le : ∫ x, x ^ 2 ∂ν ≤ hi
  moment : ∀ p : ℕ, ∫ x, |Real.sqrt N * x| ^ p ∂ν ≤ C p

/-- The upper index `(min i j, max i j)` of the entry `(i, j)`. -/
private def ecwUp {N : ℕ} (i j : Fin N) : UpperIdx N := ⟨(min i j, max i j), min_le_max⟩

/-- The variance bound of the entry `α`: `2/N` on the diagonal and `1/N` off it. -/
private def ecwVarHi (N : ℕ) (α : UpperIdx N) : ℝ :=
  if α.1.1 = α.1.2 then 2 / (N : ℝ) else 1 / N

private lemma ecw_goeLaw_prob (N : ℕ) (α : UpperIdx N) : IsProbabilityMeasure (goeLaw N α) := by
  unfold goeLaw
  infer_instance

private lemma ecw_entryLawW_prob {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : ∀ i j, Measurable fun ω => W ω i j)
    (α : UpperIdx N) : IsProbabilityMeasure (entryLawW W α) :=
  ⟨by simp [entryLawW, Measure.map_apply (hW α.1.1 α.1.2) MeasurableSet.univ]⟩

/-- The entry law `α` of a matrix in the class satisfies `EcwULaw`. -/
private lemma ecw_entryLawW_uLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N) :
    EcwULaw N C (1 / N) (ecwVarHi N α) (entryLawW W α) := by
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
    · simp only [ecwVarHi, h, ite_true]
      exact hW.var_diag_le _
    · simp only [ecwVarHi, h, ite_false]
      exact (hW.var_off _ _ h).le
  · exact (key (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le (hW.moment p _ _)

private lemma EcwULaw.mono {N : ℕ} {C C' : ℕ → ℝ} {lo hi : ℝ} {ν : Measure ℝ}
    (h : EcwULaw N C lo hi ν) (hC : ∀ p, C p ≤ C' p) : EcwULaw N C' lo hi ν :=
  ⟨h.integrable, h.mean, h.var_ge, h.var_le, fun p => (h.moment p).trans (hC p)⟩

/-- The entry law of the GOE matrix `goeW N` is `goeLaw N`. -/
private lemma ecw_entryLawW_goeW (N : ℕ) (α : UpperIdx N) : entryLawW (goeW N) α = goeLaw N α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  change i ≤ j at hij
  simp only [entryLawW, goeLaw]
  rcases hij.lt_or_eq with h | h
  · rw [(isGOE_goeW N).law_off i j h]
    simp [goeVar, h.ne]
  · subst h
    rw [(isGOE_goeW N).law_diag i]
    simp [goeVar]

/-- The GOE entry law satisfies `EcwULaw` with moments `momMaxW C`. -/
private lemma ecw_goeLaw_uLaw {N : ℕ} (hN : 1 ≤ N) (C : ℕ → ℝ) (α : UpperIdx N) :
    EcwULaw N (momMaxW C) (1 / N) (ecwVarHi N α) (goeLaw N α) := by
  rw [← ecw_entryLawW_goeW]
  exact (ecw_entryLawW_uLaw ((isGOE_goeW N).classEntries hN) α).mono
    (fun p => le_max_right _ _)

/-- `|y|^k = N^{-k/2} |√N y|^k`. -/
private lemma ecw_abs_pow_eq {N : ℕ} (hN : 1 ≤ N) (y : ℝ) (k : ℕ) :
    |y| ^ k = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * y| ^ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← mul_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn.le,
    ← Real.rpow_add hn]
  have : -(k : ℝ) / 2 + 1 / 2 * k = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-- `|∫ x³ dν| ≤ N^{-3/2} C_3` for a law with `∫ |√N x|³ dν ≤ C_3`. -/
private lemma ecw_abs_third_le {N : ℕ} (hN : 1 ≤ N) {C : ℕ → ℝ} {lo hi : ℝ} {ν : Measure ℝ}
    (h : EcwULaw N C lo hi ν) : |∫ x, x ^ 3 ∂ν| ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * max (C 3) 0 := by
  rw [← Real.norm_eq_abs]
  have hi := h.integrable 3
  refine (norm_integral_le_of_norm_le (hi.const_mul ((N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)))
    (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_pow, ecw_abs_pow_eq hN]
  · rw [integral_const_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left ((h.moment 3).trans (le_max_left _ _)) (by positivity)

/-- The upper-triangular coordinates of a symmetric matrix determine it. -/
private lemma ecw_ofUpper_restrict {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : Mᵀ = M) :
    ofUpper (fun β : UpperIdx N => M β.1.1 β.1.2) = M := by
  ext i j
  simp only [ofUpper]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact congrFun (congrFun hM i) j

/-- For a matrix of the class, the law of its upper coordinates is the product of the entry
laws. -/
private lemma ecw_integral_pi_entryLaw {Ω : Type*} [MeasureSpace Ω]
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
  rw [ecw_ofUpper_restrict (hW.symm ω)]

private lemma ecw_continuous_ofUpper {N : ℕ} :
    Continuous (ofUpper : (UpperIdx N → ℝ) → Matrix (Fin N) (Fin N) ℝ) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_apply (A := fun _ : UpperIdx N => ℝ) (ecwUp i j)

private lemma ecw_ofUpper_symm {N : ℕ} (x : UpperIdx N → ℝ) :
    (ofUpper x : Matrix (Fin N) (Fin N) ℝ)ᵀ = ofUpper x := by
  ext i j
  simp [ofUpper, min_comm, max_comm]

private lemma ecw_up_self {N : ℕ} (α : UpperIdx N) : ecwUp α.1.1 α.1.2 = α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  simp only [ecwUp]
  congr
  · exact min_eq_left hij
  · exact max_eq_right hij

/-- Updating the coordinate `α` of the upper triangle is the symmetric update of the entry
`α`. -/
private lemma ecw_ofUpper_update {N : ℕ} (x : UpperIdx N → ℝ) (α : UpperIdx N) (t : ℝ) :
    ofUpper (Function.update x α t) = Wupd (ofUpper x) α.1.1 α.1.2 t := by
  ext a b
  simp only [Wupd, ofUpper]
  by_cases h : (a = α.1.1 ∧ b = α.1.2) ∨ (a = α.1.2 ∧ b = α.1.1)
  · simp only [h, ↓reduceIte]
    have he : (⟨(min a b, max a b), min_le_max⟩ : UpperIdx N) = α := by
      obtain ⟨⟨i, j⟩, hij⟩ := α
      change i ≤ j at hij
      apply Subtype.ext
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [min_eq_left hij, max_eq_right hij]
      · simp [min_eq_right hij, max_eq_left hij]
    rw [he, Function.update_self]
  · simp only [h, ↓reduceIte]
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

end Laws

/-- The sample space of a triple `(x, y₁, y₀)` with law `μ ⊗ ν₁ ⊗ ν₀`. -/
private def EcwSpace (ι : Type) (_μ : Measure (ι → ℝ)) (_ν₁ _ν₀ : Measure ℝ) : Type :=
  (ι → ℝ) × (ℝ × ℝ)

private instance (ι : Type) (μ : Measure (ι → ℝ)) (ν₁ ν₀ : Measure ℝ) :
    MeasurableSpace (EcwSpace ι μ ν₁ ν₀) := Prod.instMeasurableSpace

private instance (ι : Type) (μ : Measure (ι → ℝ)) (ν₁ ν₀ : Measure ℝ) :
    MeasureSpace (EcwSpace ι μ ν₁ ν₀) := ⟨μ.prod (ν₁.prod ν₀)⟩

section EcwSpace

variable {ι : Type} (μ : Measure (ι → ℝ)) (ν₁ ν₀ : Measure ℝ) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₀]

private lemma ecw_prob : IsProbabilityMeasure (ℙ : Measure (EcwSpace ι μ ν₁ ν₀)) := by
  change IsProbabilityMeasure (μ.prod (ν₁.prod ν₀))
  infer_instance

omit [IsProbabilityMeasure μ] in
private lemma ecw_map_fst :
    (ℙ : Measure (EcwSpace ι μ ν₁ ν₀)).map (fun ω => (ω.1 : ι → ℝ)) = μ := by
  change (μ.prod (ν₁.prod ν₀)).map Prod.fst = μ
  rw [Measure.map_fst_prod, measure_univ, one_smul]

private lemma ecw_integral_fst (g : (ι → ℝ) → ℝ) :
    ∫ ω : EcwSpace ι μ ν₁ ν₀, g ω.1 = ∫ x, g x ∂μ := by
  change ∫ q, g q.1 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_fst, probReal_univ, one_smul]

private lemma ecw_integral_y₁ (g : ℝ → ℝ) :
    ∫ ω : EcwSpace ι μ ν₁ ν₀, g ω.2.1 = ∫ t, g t ∂ν₁ := by
  change ∫ q, (fun r : ℝ × ℝ => g r.1) q.2 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_snd (f := fun r : ℝ × ℝ => g r.1), probReal_univ, one_smul,
    integral_fun_fst (f := g), probReal_univ, one_smul]

private lemma ecw_integral_y₀ (g : ℝ → ℝ) :
    ∫ ω : EcwSpace ι μ ν₁ ν₀, g ω.2.2 = ∫ t, g t ∂ν₀ := by
  change ∫ q, (fun r : ℝ × ℝ => g r.2) q.2 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_snd (f := fun r : ℝ × ℝ => g r.2), probReal_univ, one_smul,
    integral_fun_snd (f := g), probReal_univ, one_smul]

private lemma ecw_integrable_y₁ {g : ℝ → ℝ} (hg : Integrable g ν₁) :
    Integrable fun ω : EcwSpace ι μ ν₁ ν₀ => g ω.2.1 := by
  change Integrable (fun q => (fun r : ℝ × ℝ => g r.1) q.2) (μ.prod (ν₁.prod ν₀))
  exact (hg.comp_fst ν₀).comp_snd μ

private lemma ecw_integrable_y₀ {g : ℝ → ℝ} (hg : Integrable g ν₀) :
    Integrable fun ω : EcwSpace ι μ ν₁ ν₀ => g ω.2.2 := by
  change Integrable (fun q => (fun r : ℝ × ℝ => g r.2) q.2) (μ.prod (ν₁.prod ν₀))
  exact (hg.comp_snd ν₁).comp_snd μ

omit [IsProbabilityMeasure μ] in
/-- `E g(X^θ, y₁) = ∫ g d(μ ⊗ ν₁)`. -/
private lemma ecw_integral_pair₁ {g : (ι → ℝ) × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω : EcwSpace ι μ ν₁ ν₀, g (ω.1, ω.2.1) = ∫ q, g q ∂(μ.prod ν₁) := by
  have hm : (μ.prod (ν₁.prod ν₀)).map (Prod.map id Prod.fst) = μ.prod ν₁ := by
    rw [← Measure.map_prod_map μ (ν₁.prod ν₀) measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hm, integral_map (measurable_id.prodMap measurable_fst).aemeasurable
    hg.aestronglyMeasurable]
  rfl

omit [IsProbabilityMeasure μ] in
/-- `E g(X^θ, y₀) = ∫ g d(μ ⊗ ν₀)`. -/
private lemma ecw_integral_pair₀ {g : (ι → ℝ) × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω : EcwSpace ι μ ν₁ ν₀, g (ω.1, ω.2.2) = ∫ q, g q ∂(μ.prod ν₀) := by
  have hm : (μ.prod (ν₁.prod ν₀)).map (Prod.map id Prod.snd) = μ.prod ν₀ := by
    rw [← Measure.map_prod_map μ (ν₁.prod ν₀) measurable_id measurable_snd, Measure.map_id,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hm, integral_map (measurable_id.prodMap measurable_snd).aemeasurable
    hg.aestronglyMeasurable]
  rfl

private lemma ecw_indep_fst_snd :
    IndepFun (fun ω : EcwSpace ι μ ν₁ ν₀ => (ω.1 : ι → ℝ)) (fun ω => (ω.2 : ℝ × ℝ)) := by
  change IndepFun (Prod.fst : (ι → ℝ) × (ℝ × ℝ) → _) Prod.snd (μ.prod (ν₁.prod ν₀))
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp only [Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, Measure.map_snd_prod,
    measure_univ, one_smul]

end EcwSpace

/-- The class passes to `W ∘ f` for a measure-preserving `f`. -/
private lemma ecw_class_transfer {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')] {f : Ω' → Ω}
    (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) :
    WigClassEntries C N fun ω' => W (f ω') := by
  have key : ∀ g : ℝ → ℝ, Continuous g → ∀ i j,
      ∫ ω', g (W (f ω') i j) = ∫ ω, g (W ω i j) := fun g hg i j => by
    have h := integral_map (μ := (ℙ : Measure Ω')) hf.aemeasurable (f := fun ω => g (W ω i j))
      (hg.measurable.comp (hW.measurable i j)).aestronglyMeasurable
    rw [hmap] at h
    exact h.symm
  have hmeasW : ∀ β : UpperIdx N, Measurable fun ω => W ω β.1.1 β.1.2 :=
    fun β => hW.measurable β.1.1 β.1.2
  refine ⟨fun i j => (hW.measurable i j).comp hf, fun ω' => hW.symm (f ω'), ?_,
    fun i j => ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_, fun q i j => ?_, fun q i j => ?_⟩
  · have hm' : ∀ β : UpperIdx N, AEMeasurable (fun ω' => W (f ω') β.1.1 β.1.2) ℙ :=
      fun β => ((hmeasW β).comp hf).aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map hm']
    have h := (iIndepFun_iff_map_fun_eq_pi_map (fun β => (hmeasW β).aemeasurable)).1 hW.indep
    have hg : Measurable fun ω (β : UpperIdx N) => W ω β.1.1 β.1.2 := measurable_pi_iff.2 hmeasW
    have e1 : (ℙ : Measure Ω').map (fun ω' (β : UpperIdx N) => W (f ω') β.1.1 β.1.2) =
        (ℙ : Measure Ω).map (fun ω (β : UpperIdx N) => W ω β.1.1 β.1.2) := by
      rw [← hmap, Measure.map_map hg hf]; rfl
    have e2 : ∀ β : UpperIdx N, (ℙ : Measure Ω').map (fun ω' => W (f ω') β.1.1 β.1.2) =
        (ℙ : Measure Ω).map (fun ω => W ω β.1.1 β.1.2) := fun β => by
      rw [← hmap, Measure.map_map (hmeasW β) hf]; rfl
    rw [e1, h]
    simp_rw [e2]
  · exact (key (fun t => t) continuous_id i j).trans (hW.mean i j)
  · exact (key (fun t => t ^ 2) (by fun_prop) i j).trans (hW.var_off i j hij)
  · exact (hW.var_diag_ge i).trans_eq (key (fun t => t ^ 2) (by fun_prop) i i).symm
  · exact (key (fun t => t ^ 2) (by fun_prop) i i).trans_le (hW.var_diag_le i)
  · have hc : Continuous fun t : ℝ => |Real.sqrt N * t| ^ q := by fun_prop
    have h := hW.integrable_moment q i j
    have h1 : Integrable (fun t : ℝ => |Real.sqrt N * t| ^ q)
        ((ℙ : Measure Ω').map fun ω => W (f ω) i j) := by
      rw [show (fun ω => W (f ω) i j) = (fun ω => W ω i j) ∘ f from rfl,
        ← Measure.map_map (hW.measurable i j) hf, hmap]
      exact (integrable_map_measure hc.aestronglyMeasurable (hW.measurable i j).aemeasurable).2 h
    exact (integrable_map_measure hc.aestronglyMeasurable
      ((hW.measurable i j).comp hf).aemeasurable).1 h1
  · exact (key (fun t => |Real.sqrt N * t| ^ q) (by fun_prop) i j).trans_le (hW.moment q i j)
/-! ## The smoothed counts as functions of the entries -/

section Functional

variable {N : ℕ}

/-- `x ↦ 𝒳_{[E₁,E₂]}(ofUpper x + A)` is continuous. -/
private lemma ecw_continuous_smCount_up {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    Continuous fun x : UpperIdx N → ℝ => smCount (ofUpper x + A) η E₁ E₂ := by
  have hH : ∀ x : UpperIdx N → ℝ, (ofUpper x + A).IsHermitian := fun x =>
    (ecw_herm_of_symm (ecw_ofUpper_symm x)).add hA
  have he : (fun x : UpperIdx N → ℝ => smCount (ofUpper x + A) η E₁ E₂) = fun x =>
      Real.pi⁻¹ * ∫ y in E₁..E₂, (trace (GW A (ofUpper x) ((y : ℂ) + η * Complex.I))).im := by
    funext x
    exact ecw_smCount_eq (hH x) hη E₁ E₂
  rw [he]
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : UpperIdx N → ℝ) (y : ℝ) =>
      (trace (GW A (ofUpper x) ((y : ℂ) + η * Complex.I))).im) ?_ E₁ E₂
  have hG := ecw_continuous_GW A (Wf := fun p : (UpperIdx N → ℝ) × ℝ => ofUpper p.1)
    (zf := fun p : (UpperIdx N → ℝ) × ℝ => ((p.2 : ℝ) : ℂ) + η * Complex.I)
    (ecw_continuous_ofUpper.comp continuous_fst)
    ((Complex.continuous_ofReal.comp continuous_snd).add continuous_const)
    (fun p => hH p.1) fun _ => by simpa using hη
  exact Complex.continuous_im.comp hG.matrix_trace

/-- For symmetric `A`, a sum over the spectrum is a sum over the ordered eigenvalues. -/
private lemma ecw_sum_specOf {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (φ : ℝ → ℝ) :
    ∑ j, φ (specOf A j) = ∑ k : Fin (Fintype.card (Fin n)), φ (sortedEig A (k + 1)) := by
  rw [specOf_eq hA]
  unfold Matrix.IsHermitian.eigenvalues
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => φ (hA.eigenvalues₀ k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hk := k.2
  unfold sortedEig
  rw [dite_eq_left ⟨hA, by omega, by omega⟩]
  congr 1

/-- `F((𝒳_{[Ea_k, Eb_k]}(H))_k)` through the ordered eigenvalues of `H`; it is measurable in `H`
and invariant under orthogonal conjugation of symmetric matrices. -/
private def ecwPhi {l : ℕ} (F : (Fin l → ℝ) → ℝ) (η : ℝ) (Ea Eb : Fin l → ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  F fun k => ∑ k' : Fin (Fintype.card (Fin N)),
    (Real.arctan ((Eb k - sortedEig H (k' + 1)) / η) -
      Real.arctan ((Ea k - sortedEig H (k' + 1)) / η)) / Real.pi

private lemma ecwPhi_eq {l : ℕ} (F : (Fin l → ℝ) → ℝ) (η : ℝ) (Ea Eb : Fin l → ℝ)
    {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    ecwPhi F η Ea Eb H = F fun k => smCount H η (Ea k) (Eb k) := by
  unfold ecwPhi smCount
  congr 1
  funext k
  exact (ecw_sum_specOf hH (fun x =>
    (Real.arctan ((Eb k - x) / η) - Real.arctan ((Ea k - x) / η)) / Real.pi)).symm

private lemma ecwPhi_measurable {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : Continuous F) (η : ℝ)
    (Ea Eb : Fin l → ℝ) : Measurable (ecwPhi (N := N) F η Ea Eb) := by
  unfold ecwPhi
  refine hF.measurable.comp (measurable_pi_iff.2 fun k => Finset.measurable_sum _ fun k' _ => ?_)
  have hc : Continuous fun x : ℝ =>
      (Real.arctan ((Eb k - x) / η) - Real.arctan ((Ea k - x) / η)) / Real.pi := by fun_prop
  exact hc.measurable.comp (measurable_sortedEig' N _)

private lemma ecwPhi_conj {l : ℕ} (F : (Fin l → ℝ) → ℝ) (η : ℝ) (Ea Eb : Fin l → ℝ)
    (O : Matrix (Fin N) (Fin N) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) (hX : X.IsHermitian) :
    ecwPhi F η Ea Eb (O * X * Oᵀ) = ecwPhi F η Ea Eb X := by
  have hOX : (O * X * Oᵀ).IsHermitian := by
    have := Matrix.isHermitian_mul_mul_conjTranspose O hX
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  rw [ecwPhi_eq F η Ea Eb hOX, ecwPhi_eq F η Ea Eb hX]
  unfold smCount
  rw [specOf_conj hO]

end Functional

/-! ## Sums over the upper-triangular indices and the exponent bookkeeping of the comparison -/

section CmpArith

variable {N : ℕ}

/-- A sum over `{i ≤ j}` as a double sum. -/
private lemma ecw_sum_upper (g : Fin N → Fin N → ℝ) :
    ∑ α : UpperIdx N, g α.1.1 α.1.2 = ∑ i, ∑ j, if i ≤ j then g i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≤ p.2)
    (fun p => by simp) (fun p : Fin N × Fin N => g p.1 p.2), Finset.sum_filter,
    Fintype.sum_prod_type]

/-- `Q ≤ N^a` once `⌈Q^{1/a}⌉ ≤ N`. -/
private lemma ecw_le_rpow {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) {N : ℕ}
    (h : ⌈Q ^ a⁻¹⌉₊ ≤ N) : Q ≤ (N : ℝ) ^ a := by
  have h1 : Q ^ a⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  calc Q = (Q ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hQ ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hQ _) h1 ha.le

/-- The off-diagonal swaps `N² N^{-7/3+12ε}`, the diagonal swaps `N N^{-4/3+12ε}` and the
third-order sum `N^{-3/2} N^{4/3+22ε}` together are at most `C_b N^{-(1/6-24ε)}` once the
constants are below `N^{2ε}`. -/
private lemma ecw_cmp_final (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    {Ko Kd Kt c3 Cb : ℝ} (hKo : 0 ≤ Ko) (hKd : 0 ≤ Kd) (hCb : 0 ≤ Cb)
    (hA : Ko + Kd + Kt * c3 / 3 ≤ (N : ℝ) ^ (2 * ε)) :
    (N : ℝ) ^ 2 * (Ko * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε)) +
        N * (Kd * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε)) +
        Kt * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3 / 3) * Cb * (N : ℝ) ^ (4 / 3 + 22 * ε) ≤
      Cb * (N : ℝ) ^ (-(1 / 6 - 24 * ε)) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  set P := (N : ℝ) ^ (-1 / 6 + 22 * ε) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hn.le _
  have e1 : (N : ℝ) ^ 2 * (N : ℝ) ^ (-7 / 3 + 12 * ε) = (N : ℝ) ^ (-1 / 3 + 12 * ε) := by
    rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_add hn]
    congr 1; push_cast; ring
  have e2 : (N : ℝ) * (N : ℝ) ^ (-4 / 3 + 12 * ε) = (N : ℝ) ^ (-1 / 3 + 12 * ε) := by
    rw [show (N : ℝ) * (N : ℝ) ^ (-4 / 3 + 12 * ε) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-4 / 3 + 12 * ε)
      by rw [Real.rpow_one], ← Real.rpow_add hn]
    congr 1; ring
  have e3 : (N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (4 / 3 + 22 * ε) = P := by
    rw [hP, ← Real.rpow_add hn]; congr 1; ring
  have h12 : (N : ℝ) ^ (-1 / 3 + 12 * ε) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have e4 : (N : ℝ) ^ (2 * ε) * P = (N : ℝ) ^ (-(1 / 6 - 24 * ε)) := by
    rw [hP, ← Real.rpow_add hn]; congr 1; ring
  have t1 : (N : ℝ) ^ 2 * (Ko * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε)) ≤ Ko * Cb * P := by
    rw [show (N : ℝ) ^ 2 * (Ko * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε)) =
      Ko * Cb * ((N : ℝ) ^ 2 * (N : ℝ) ^ (-7 / 3 + 12 * ε)) by ring, e1]
    exact mul_le_mul_of_nonneg_left h12 (mul_nonneg hKo hCb)
  have t2 : (N : ℝ) * (Kd * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε)) ≤ Kd * Cb * P := by
    rw [show (N : ℝ) * (Kd * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε)) =
      Kd * Cb * ((N : ℝ) * (N : ℝ) ^ (-4 / 3 + 12 * ε)) by ring, e2]
    exact mul_le_mul_of_nonneg_left h12 (mul_nonneg hKd hCb)
  have t3 : Kt * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3 / 3) * Cb * (N : ℝ) ^ (4 / 3 + 22 * ε) =
      Kt * c3 / 3 * Cb * P := by
    rw [← e3]; ring
  rw [t3, ← e4]
  have : (Ko + Kd + Kt * c3 / 3) * (Cb * P) ≤ (N : ℝ) ^ (2 * ε) * (Cb * P) :=
    mul_le_mul_of_nonneg_right hA (mul_nonneg hCb hP0)
  nlinarith

end CmpArith
/-! ## The comparison step

Lindeberg interpolation between the GOE and `W` over the upper-triangular entries
(Definition 7.6 with `ι = {i ≤ j}`) in the proof of Theorem 12.5, on the comparison window. -/

/-- The comparison step for `W + A` (`SmoothComparable`) against `W^Gauss + D`, with
`c₁ = 1/6 - 24ε`: Lindeberg interpolation over `{i ≤ j}` between the GOE and `W`, the swaps,
the third-order sum, and the orthogonal invariance of the GOE. -/
theorem smoothComparable_wig (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ)
    (hτ4 : τ ≤ 1 / 4) (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      SmoothComparable N (LpW (specOf A)) ε (1 / 6 - 24 * ε) l (fun ω => W ω + A)
        (fun ω => goeW N ω + diagonal (specOf A)) := by
  obtain ⟨εo, Do, hεo, Ko, No, hoff⟩ := smFW_swap_off τ (momMaxW C) l ε hτ hτ4 hε hε1
  obtain ⟨εd, Dd, hεd, Kd, Nd, hdiag⟩ := smFW_swap_diag τ (momMaxW C) l ε hτ hτ4 hε hε1
  obtain ⟨εt, Dt, hεt, Kt, Nt, hthird⟩ := smTW_third_sum τ (momMaxW C) l ε hτ hτ4 hε hε1
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℝ, c3 = max (momMaxW C 3) 0 := ⟨_, rfl⟩
  have hc30 : 0 ≤ c3 := by rw [hc3]; exact le_max_right _ _
  have hKo0 := le_max_right Ko 0
  have hKd0 := le_max_right Kd 0
  have hKt0 := le_max_right Kt 0
  obtain ⟨KA, hKA⟩ : ∃ KA : ℝ, KA = max Ko 0 + max Kd 0 + max Kt 0 * c3 / 3 := ⟨_, rfl⟩
  have hKA0 : 0 ≤ KA := by rw [hKA]; positivity
  refine ⟨min εo (min εd εt), max Do (max Dd Dt), lt_min hεo (lt_min hεd hεt),
    max (max No Nd) (max Nt (max ⌈KA ^ (2 * ε)⁻¹⌉₊ 1)), ?_⟩
  intro N hN Ω _ _ A W hA hnA hW hSB hlawG F Cb hF hFb E hE
  have hNo : No ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNd : Nd ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNt : Nt ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNA : ⌈KA ^ (2 * ε)⁻¹⌉₊ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN1 : 1 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn : (0 : ℝ) < N := by linarith
  have hη : 0 < etaE N ε := by unfold etaE; positivity
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hFB : ∀ x, |F x| ≤ Cb := fun x => by
    have := hFb 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  -- the entrywise law of the GOE at each of the exponents
  have hlaw' : ∀ ε' D', min εo (min εd εt) ≤ ε' → D' ≤ max Do (max Dd Dt) →
      EntrywiseLawWAt N ε' D' (diagonal (specOf A)) (goeW N) (domW τ N) := by
    intro ε' D' h1 h2 z hz s t
    refine DomAt.mono hN1 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => ?_) h1 h2 (hlawG z hz s t)
    unfold PsiW
    exact add_nonneg (Real.sqrt_nonneg _)
      (div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hz.1.le))
  have hlo := hlaw' εo Do (min_le_left _ _) (le_max_left _ _)
  have hld := hlaw' εd Dd ((min_le_right _ _).trans (min_le_left _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
  have hlt := hlaw' εt Dt ((min_le_right _ _).trans (min_le_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  -- the windows
  obtain ⟨Eb, hEb⟩ : ∃ Eb : Fin l → ℝ, Eb = fun _ => edgeEL N (LpW (specOf A)) ε := ⟨_, rfl⟩
  have hwinE : ∀ k, |E k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) ∧
      |Eb k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) := by
    intro k
    have h0 : 0 ≤ (N : ℝ) ^ (-2 / 3 + ε) := Real.rpow_nonneg hn.le _
    refine ⟨(hE k).trans (by linarith), ?_⟩
    rw [hEb, edgeEL, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    linarith
  -- the GOE side: `W^Gauss + D` against `W^Gauss + A`
  have hHA : ∀ ω, (goeW N ω + A).IsHermitian := fun ω =>
    (ecw_herm_of_symm ((isGOE_goeW N).symm ω)).add hA
  have hHD : ∀ ω, (goeW N ω + diagonal (specOf A)).IsHermitian := fun ω =>
    (ecw_herm_of_symm ((isGOE_goeW N).symm ω)).add (Matrix.isHermitian_diagonal _)
  have hgoe : (∫ ω, F fun j => smCount (goeW N ω + diagonal (specOf A)) (etaE N ε) (E j)
      (edgeEL N (LpW (specOf A)) ε)) = ∫ ω, smFW F A (goeW N ω) (etaE N ε) E Eb := by
    have h := integral_goe_add_conj hA (ecwPhi_measurable hF.continuous (etaE N ε) E Eb)
      (ecwPhi_conj F (etaE N ε) E Eb)
    have e1 : (fun ω => ecwPhi F (etaE N ε) E Eb (goeW N ω + A)) =
        fun ω => smFW F A (goeW N ω) (etaE N ε) E Eb :=
      funext fun ω => ecwPhi_eq F (etaE N ε) E Eb (hHA ω)
    have e2 : (fun ω => ecwPhi F (etaE N ε) E Eb (goeW N ω + diagonal (specOf A))) =
        fun ω => F fun j => smCount (goeW N ω + diagonal (specOf A)) (etaE N ε) (E j)
          (edgeEL N (LpW (specOf A)) ε) :=
      funext fun ω => by rw [ecwPhi_eq F (etaE N ε) E Eb (hHD ω), hEb]
    rw [e1, e2] at h
    exact h.symm
  rw [hgoe]
  have hW1 : (fun ω => F fun j => smCount (W ω + A) (etaE N ε) (E j)
      (edgeEL N (LpW (specOf A)) ε)) = fun ω => smFW F A (W ω) (etaE N ε) E Eb := by
    rw [hEb]; rfl
  rw [hW1]
  -- the laws of `W`, the GOE and the function `Φ = F ∘ 𝒳 ∘ ofUpper`
  set ρ₀ : UpperIdx N → Measure ℝ := goeLaw N with hρ₀
  set ρ₁ : UpperIdx N → Measure ℝ := entryLawW W with hρ₁
  have : ∀ α, IsProbabilityMeasure (ρ₀ α) := ecw_goeLaw_prob N
  have : ∀ α, IsProbabilityMeasure (ρ₁ α) := ecw_entryLawW_prob hW.measurable
  set Φ : (UpperIdx N → ℝ) → ℝ := fun x => smFW F A (ofUpper x) (etaE N ε) E Eb with hΦ
  have hΦc : Continuous Φ := hF.continuous.comp (continuous_pi fun k =>
    ecw_continuous_smCount_up hA hη (E k) (Eb k))
  have hΦm : Measurable Φ := hΦc.measurable
  have hΦi : ∀ (ν : Measure (UpperIdx N → ℝ)) [IsFiniteMeasure ν], Integrable Φ ν :=
    fun ν _ => Integrable.of_bound hΦm.aestronglyMeasurable Cb
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFB _)
  have hvert : ∀ u, Integrable Φ (vertexLaw ρ₀ ρ₁ u) := fun u => by
    have : ∀ α, IsProbabilityMeasure (if u α then ρ₁ α else ρ₀ α) := fun α => by
      split <;> infer_instance
    have : IsProbabilityMeasure (vertexLaw ρ₀ ρ₁ u) := by unfold vertexLaw; infer_instance
    exact hΦi _
  have hX1 : ∫ ω, smFW F A (W ω) (etaE N ε) E Eb = ∫ x, Φ x ∂(Measure.pi ρ₁) :=
    (ecw_integral_pi_entryLaw (F := fun M => smFW F A M (etaE N ε) E Eb) hW hΦm).symm
  have hρ₀e : ρ₀ = entryLawW (goeW N) := funext fun α => (ecw_entryLawW_goeW N α).symm
  have hX0 : ∫ ω, smFW F A (goeW N ω) (etaE N ε) E Eb = ∫ x, Φ x ∂(Measure.pi ρ₀) := by
    rw [hρ₀e]
    exact (ecw_integral_pi_entryLaw (F := fun M => smFW F A M (etaE N ε) E Eb)
      ((isGOE_goeW N).classEntries hN1) hΦm).symm
  rw [hX1, hX0, interpol hΦm hvert]
  -- the bound for every `θ ∈ [0, 1]`
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = (N : ℝ) ^ (-(3 : ℝ) / 2) * c3 / 3 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (N : ℝ) ^ 2 * (max Ko 0 * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε)) +
      N * (max Kd 0 * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε)) +
      max Kt 0 * S * Cb * (N : ℝ) ^ (4 / 3 + 22 * ε) := ⟨_, rfl⟩
  have hθ : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |∑ α, ((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
      ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)))| ≤ B := by
    intro θ hθ
    have hmixP : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
      fun β => isProbabilityMeasure_mixMeasure _ _ _
    have hIP : IsProbabilityMeasure (interpLaw θ ρ₀ ρ₁) := by unfold interpLaw; infer_instance
    have : IsProbabilityMeasure (ℙ : Measure (InterpSpace (UpperIdx N) θ ρ₀ ρ₁)) := hIP
    have hWθ : WigClassEntries (momMaxW C) (Ω := InterpSpace (UpperIdx N) θ ρ₀ ρ₁) N ofUpper :=
      wigClass_interp hN1 hW hθ.1 hθ.2
    have hAt : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (α : UpperIdx N),
        IsProbabilityMeasure (interpLawAt θ ρ₀ ρ₁ α ρ) := by
      intro ρ _ α
      have : ∀ β', IsProbabilityMeasure
          (Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ β') := fun β' => by
        by_cases h : β' = α
        · rw [h, Function.update_self]; infer_instance
        · rw [Function.update_of_ne h]; exact hmixP β'
      unfold interpLawAt
      infer_instance
    set T : Fin N → Fin N → ℝ := fun i j => ∫ x, smTW 3 F A (ofUpper x) (etaE N ε) E Eb i j
      (ofUpper x i j) ∂(interpLaw θ ρ₀ ρ₁) with hTdef
    set s : Fin N → Fin N → ℝ := fun i j =>
      ((∫ t, t ^ 3 ∂(ρ₁ (ecwUp i j))) - ∫ t, t ^ 3 ∂(ρ₀ (ecwUp i j))) / 6 with hsdef
    have hs : ∀ i j, |s i j| ≤ S := by
      intro i j
      have h1 := ecw_abs_third_le hN1 (EcwULaw.mono (C' := momMaxW C)
        (ecw_entryLawW_uLaw hW (ecwUp i j)) fun p => le_max_left _ _)
      have h0 := ecw_abs_third_le hN1 (ecw_goeLaw_uLaw hN1 C (ecwUp i j))
      rw [← hc3] at h1 h0
      simp only [hsdef, hSdef]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      have := abs_sub (∫ t, t ^ 3 ∂(ρ₁ (ecwUp i j))) (∫ t, t ^ 3 ∂(ρ₀ (ecwUp i j)))
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
      linarith
    have h3 : |∑ i, ∑ j, if i < j then s i j * T i j else 0| ≤
        Kt * S * Cb * (N : ℝ) ^ (4 / 3 + 22 * ε) :=
      hthird N hNt (Ω := InterpSpace (UpperIdx N) θ ρ₀ ρ₁) A ofUpper s S F Cb E Eb hA hnA hWθ
        hSB hlt hs hF hFb hwinE
    -- one entry: the swap of `y₁ ∼` the law of `W_α` against `y₀ ∼` the GOE law in `W^θ`
    have hent : ∀ α : UpperIdx N, |((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
        ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) -
          (if α.1.1 < α.1.2 then s α.1.1 α.1.2 * T α.1.1 α.1.2 else 0)| ≤
        if α.1.1 < α.1.2 then max Ko 0 * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε)
          else max Kd 0 * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε) := by
      intro α
      have : IsProbabilityMeasure
          (ℙ : Measure (EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α))) :=
        ecw_prob _ _ _
      have hfm : Measurable fun ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          (ω.1 : InterpSpace (UpperIdx N) θ ρ₀ ρ₁) := measurable_fst
      have hW' := ecw_class_transfer (Ω := InterpSpace (UpperIdx N) θ ρ₀ ρ₁) hfm
        (by exact ecw_map_fst (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) hWθ
      have hind := ecw_indep_fst_snd (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)
      have hind1 : IndepFun (fun ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          ofUpper (ω.1 : UpperIdx N → ℝ)) (fun ω => (ω.2.1 : ℝ)) :=
        hind.comp ecw_continuous_ofUpper.measurable measurable_fst
      have hind0 : IndepFun (fun ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          ofUpper (ω.1 : UpperIdx N → ℝ)) (fun ω => (ω.2.2 : ℝ)) :=
        hind.comp ecw_continuous_ofUpper.measurable measurable_snd
      have u1 : EcwULaw N (momMaxW C) (1 / N) (ecwVarHi N α) (ρ₁ α) :=
        EcwULaw.mono (C' := momMaxW C) (ecw_entryLawW_uLaw hW α) fun p => le_max_left _ _
      have u0 : EcwULaw N (momMaxW C) (1 / N) (ecwVarHi N α) (ρ₀ α) := ecw_goeLaw_uLaw hN1 C α
      have hmean1 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
          (ω.2.1 : ℝ) = 0 := (ecw_integral_y₁ _ _ _ (fun t => t)).trans u1.mean
      have hmean0 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
          (ω.2.2 : ℝ) = 0 := (ecw_integral_y₀ _ _ _ (fun t => t)).trans u0.mean
      have hv1 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
          (ω.2.1 : ℝ) ^ 2 = ∫ t, t ^ 2 ∂(ρ₁ α) := ecw_integral_y₁ _ _ _ (fun t => t ^ 2)
      have hv0 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
          (ω.2.2 : ℝ) ^ 2 = ∫ t, t ^ 2 ∂(ρ₀ α) := ecw_integral_y₀ _ _ _ (fun t => t ^ 2)
      have hmom1 : ∀ p : ℕ, Integrable (fun ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁)
          (ρ₁ α) (ρ₀ α) => |Real.sqrt N * (ω.2.1 : ℝ)| ^ p) ∧
          ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            |Real.sqrt N * (ω.2.1 : ℝ)| ^ p ≤ momMaxW C p := fun p =>
        ⟨ecw_integrable_y₁ _ _ _ (u1.integrable p),
          (ecw_integral_y₁ _ _ _ (fun t => |Real.sqrt N * t| ^ p)).trans_le (u1.moment p)⟩
      have hmom0 : ∀ p : ℕ, Integrable (fun ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁)
          (ρ₁ α) (ρ₀ α) => |Real.sqrt N * (ω.2.2 : ℝ)| ^ p) ∧
          ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            |Real.sqrt N * (ω.2.2 : ℝ)| ^ p ≤ momMaxW C p := fun p =>
        ⟨ecw_integrable_y₀ _ _ _ (u0.integrable p),
          (ecw_integral_y₀ _ _ _ (fun t => |Real.sqrt N * t| ^ p)).trans_le (u0.moment p)⟩
      have e1 : ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α)) =
          ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smFW F A (Wupd (ofUpper (ω.1 : UpperIdx N → ℝ)) α.1.1 α.1.2 (ω.2.1 : ℝ))
              (etaE N ε) E Eb := by
        have := hAt (ρ₁ α) α
        rw [integral_interpLawAt_eq α (ρ₁ α) hΦm (hΦi _), ← ecw_integral_pair₁
          (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) (g := fun q => Φ (Function.update q.1 α q.2))
          (hΦm.comp measurable_update')]
        simp only [hΦ, ecw_ofUpper_update]
      have e0 : ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)) =
          ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smFW F A (Wupd (ofUpper (ω.1 : UpperIdx N → ℝ)) α.1.1 α.1.2 (ω.2.2 : ℝ))
              (etaE N ε) E Eb := by
        have := hAt (ρ₀ α) α
        rw [integral_interpLawAt_eq α (ρ₀ α) hΦm (hΦi _), ← ecw_integral_pair₀
          (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) (g := fun q => Φ (Function.update q.1 α q.2))
          (hΦm.comp measurable_update')]
        simp only [hΦ, ecw_ofUpper_update]
      rw [e1, e0]
      split_ifs with hlt
      · -- an off-diagonal entry
        have hne : α.1.1 ≠ α.1.2 := hlt.ne
        have hvh : ecwVarHi N α = 1 / N := by simp [ecwVarHi, hne]
        have hvar1 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            (ω.2.1 : ℝ) ^ 2 = 1 / (N : ℝ) := by
          rw [hv1]; exact le_antisymm (hvh ▸ u1.var_le) u1.var_ge
        have hvar0 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            (ω.2.2 : ℝ) ^ 2 = 1 / (N : ℝ) := by
          rw [hv0]; exact le_antisymm (hvh ▸ u0.var_le) u0.var_ge
        have hsw := hoff N hNo (Ω := EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) A
          (fun ω => ofUpper (ω.1 : UpperIdx N → ℝ)) (fun ω => (ω.2.1 : ℝ))
          (fun ω => (ω.2.2 : ℝ)) α.1.1 α.1.2 F Cb E Eb hA hnA hW' hSB hlo hlt hind1 hind0
          (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd) hmean1 hmean0
          hvar1 hvar0 hmom1 hmom0 hF hFb hwinE
        have a1 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            (ω.2.1 : ℝ) ^ 3 = ∫ t, t ^ 3 ∂(ρ₁ α) := ecw_integral_y₁ _ _ _ (fun t => t ^ 3)
        have a0 : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            (ω.2.2 : ℝ) ^ 3 = ∫ t, t ^ 3 ∂(ρ₀ α) := ecw_integral_y₀ _ _ _ (fun t => t ^ 3)
        have tT : ∫ ω : EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smTW 3 F A (ofUpper (ω.1 : UpperIdx N → ℝ)) (etaE N ε) E Eb α.1.1 α.1.2
              (ofUpper (ω.1 : UpperIdx N → ℝ) α.1.1 α.1.2) = T α.1.1 α.1.2 :=
          ecw_integral_fst _ _ _ (fun x => smTW 3 F A (ofUpper x) (etaE N ε) E Eb α.1.1 α.1.2
            (ofUpper x α.1.1 α.1.2))
        have hsα : s α.1.1 α.1.2 = ((∫ t, t ^ 3 ∂(ρ₁ α)) - ∫ t, t ^ 3 ∂(ρ₀ α)) / 6 := by
          simp only [hsdef, ecw_up_self]
        rw [a1, a0, tT, ← hsα] at hsw
        exact hsw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) hCb) (Real.rpow_nonneg hn.le _))
      · -- a diagonal entry
        have heq : α.1.1 = α.1.2 := le_antisymm α.2 (not_lt.1 hlt)
        have hvh : ecwVarHi N α = 2 / N := by simp [ecwVarHi, heq]
        rw [sub_zero]
        have hsw := hdiag N hNd (Ω := EcwSpace (UpperIdx N) (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) A
          (fun ω => ofUpper (ω.1 : UpperIdx N → ℝ)) (fun ω => (ω.2.1 : ℝ))
          (fun ω => (ω.2.2 : ℝ)) α.1.1 F Cb E Eb hA hnA hW' hSB hld hind1 hind0
          (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd) hmean1 hmean0
          (hv1 ▸ u1.var_ge) (hv1 ▸ hvh ▸ u1.var_le) (hv0 ▸ u0.var_ge) (hv0 ▸ hvh ▸ u0.var_le)
          hmom1 hmom0 hF hFb hwinE
        rw [← heq]
        exact hsw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) hCb) (Real.rpow_nonneg hn.le _))
    -- the sum over the entries
    set Lα : UpperIdx N → ℝ := fun α => (∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
      ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)) with hLα
    have hsplit : ∑ α, Lα α = ∑ α, (Lα α -
        (if α.1.1 < α.1.2 then s α.1.1 α.1.2 * T α.1.1 α.1.2 else 0)) +
        ∑ α : UpperIdx N, (if α.1.1 < α.1.2 then s α.1.1 α.1.2 * T α.1.1 α.1.2 else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hcorr : ∑ α : UpperIdx N, (if α.1.1 < α.1.2 then s α.1.1 α.1.2 * T α.1.1 α.1.2 else 0) =
        ∑ i, ∑ j, if i < j then s i j * T i j else 0 := by
      have h := ecw_sum_upper (fun i j => if i < j then s i j * T i j else 0)
      rw [h]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · simp [hij, hij.le]
      · simp [hij]
    obtain ⟨ko, hko⟩ : ∃ ko : ℝ, ko = max Ko 0 * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε) := ⟨_, rfl⟩
    obtain ⟨kd, hkd⟩ : ∃ kd : ℝ, kd = max Kd 0 * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε) := ⟨_, rfl⟩
    have hko0 : 0 ≤ ko := by rw [hko]; positivity
    have hkd0 : 0 ≤ kd := by rw [hkd]; positivity
    have hrest : |∑ α, (Lα α - (if α.1.1 < α.1.2 then s α.1.1 α.1.2 * T α.1.1 α.1.2 else 0))| ≤
        (N : ℝ) ^ 2 * ko + N * kd := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun α _ => hent α).trans ?_
      rw [← hko, ← hkd]
      have h := ecw_sum_upper (N := N) (fun i j => if i < j then ko else kd)
      rw [h]
      calc ∑ i, ∑ j, (if i ≤ j then (if i < j then ko else kd) else 0) ≤
          ∑ i : Fin N, ∑ j : Fin N, (ko + if i = j then kd else 0) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hij : i < j
            · simp [hij, hij.le, hij.ne]
            · by_cases hle : i ≤ j
              · have heq : i = j := le_antisymm hle (not_lt.1 hij)
                simp [heq, hko0]
              · simp only [hle, ite_false]
                split_ifs <;> linarith
        _ = (N : ℝ) ^ 2 * ko + N * kd := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
            ring
    rw [hsplit, hcorr]
    refine (abs_add_le _ _).trans ?_
    have hX0 : 0 ≤ (N : ℝ) ^ (4 / 3 + 22 * ε) := Real.rpow_nonneg hn.le _
    have h3' : |∑ i, ∑ j, if i < j then s i j * T i j else 0| ≤
        max Kt 0 * S * Cb * (N : ℝ) ^ (4 / 3 + 22 * ε) :=
      h3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hS0) hCb) hX0)
    rw [hB, ← hko, ← hkd]
    linarith
  -- the integral over `θ`
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B)
    (f := fun θ => ∑ α, ((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
      ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))))
    (fun θ hθ' => by
      rw [Set.uIoc_of_le zero_le_one] at hθ'
      rw [Real.norm_eq_abs]
      exact hθ θ ⟨hθ'.1.le, hθ'.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  refine hint.trans ?_
  rw [hB, hSdef]
  exact ecw_cmp_final hN1 hε hε1 hKo0 hKd0 hCb
    (by rw [← hKA]; exact ecw_le_rpow hKA0 (by positivity) hNA)
#print axioms smTW_third_sum
#print axioms smoothComparable_wig

end Anisotropic
