module

public import Anisotropic.EdgeUniv.SmCount
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Wigner.Defs
public import Anisotropic.Wigner.EdgeDefs
public import Anisotropic.Wigner.Model
public import Anisotropic.Wigner.Taylor
public import Anisotropic.Wigner.Words
public import Anisotropic.Wigner.EdgeLocal

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # The one-entry swaps for the smoothed counts of `W + A` (off-diagonal and diagonal entries) -/

/-- `F((𝒳_{[Ea_j, Eb_j]}(W + A))_j)`. -/
def smFW {l : ℕ} (F : (Fin l → ℝ) → ℝ) {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
    (Ea Eb : Fin l → ℝ) : ℝ :=
  F (fun j => smCount (Wm + A) η (Ea j) (Eb j))

/-- The `n`-th derivative of `smFW` in the symmetric entry `(i, j)`, at the value `u` of that
entry. -/
def smTW {l : ℕ} (n : ℕ) (F : (Fin l → ℝ) → ℝ) {N : ℕ} (A Wm : Matrix (Fin N) (Fin N) ℝ)
    (η : ℝ) (Ea Eb : Fin l → ℝ) (i j : Fin N) (u : ℝ) : ℝ :=
  iteratedDeriv n (fun t => smFW F A (Wupd Wm i j t) η Ea Eb) u

/-! ## The resolvent of a real symmetric matrix -/

section Resolvent

variable {N : ℕ}

private lemma esw_symm_of_herm {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  have h := hA.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at h

private lemma esw_herm_of_symm {A : Matrix (Fin N) (Fin N) ℝ} (hA : Aᵀ = A) : A.IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- A real symmetric `H = U diag(λ) Uᵀ` with `U` real orthogonal. -/
private lemma esw_eig_decomp {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
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

private lemma esw_cplx_orth {U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1) :
    cplx U * (cplx U)ᵀ = 1 := by
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
  simp only [cplx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_map] at h ⊢
  exact h

/-- `(H − z)` times the rotated diagonal `(λₖ − z)⁻¹` is the identity. -/
private lemma esw_right_inv {H U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1)
    (hUU' : Uᵀ * U = 1) (hHU : H = U * diagonal (specOf H) * Uᵀ) {z : ℂ} (hz : 0 < z.im) :
    (cplx H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      (cplx U * diagonal (fun k => ((specOf H k : ℂ) - z)⁻¹) * (cplx U)ᵀ) = 1 := by
  have hP := esw_cplx_orth hUU
  have hP' := esw_cplx_orth (U := Uᵀ) (by rw [Matrix.transpose_transpose]; exact hUU')
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
private lemma esw_GW_eq {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * GW A Wm z = 1 ∧
      GW A Wm z = cplx U * diagonal (fun k => ((specOf (Wm + A) k : ℂ) - z)⁻¹) * (cplx U)ᵀ := by
  obtain ⟨U, hUU, hUU', hHU⟩ := esw_eig_decomp hH
  have hR := esw_right_inv hUU hUU' hHU hz
  have hG : GW A Wm z = cplx U * diagonal (fun k => ((specOf (Wm + A) k : ℂ) - z)⁻¹) *
      (cplx U)ᵀ := Matrix.inv_eq_right_inv hR
  exact ⟨U, hUU, by rw [hG]; exact hR, hG⟩

private lemma esw_mul_GW {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * GW A Wm z = 1 :=
  (esw_GW_eq hH hz).choose_spec.2.1

private lemma esw_GW_mul {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    GW A Wm z * (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 :=
  mul_eq_one_comm.1 (esw_mul_GW hH hz)

private lemma esw_isUnit {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
  Matrix.isUnit_det_of_right_inverse (esw_mul_GW hH hz)

/-- `tr G^W(z) = ∑ₖ (λₖ − z)⁻¹`. -/
private lemma esw_trace_GW {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    trace (GW A Wm z) = ∑ k, ((specOf (Wm + A) k : ℂ) - z)⁻¹ := by
  obtain ⟨U, hUU, -, hG⟩ := esw_GW_eq hH hz
  have hP := esw_cplx_orth hUU
  have hP' : (cplx U)ᵀ * cplx U = 1 := mul_eq_one_comm.1 hP
  rw [hG, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.trace_diagonal]

/-- `|(λ − z)⁻¹| ≤ (Im z)⁻¹`. -/
private lemma esw_norm_inv_le (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  have h1 : z.im ≤ ‖(x : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hz] at this
    exact this
  have h2 : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le hz h1
  rw [norm_inv, one_div]
  exact inv_anti₀ hz h1

/-- The entries of `G^W(z)` are at most `(Im z)⁻¹` in modulus. -/
private lemma esw_GW_entry_le {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (s t : Fin N) : ‖GW A Wm z s t‖ ≤ 1 / z.im := by
  obtain ⟨U, hUU, -, hG⟩ := esw_GW_eq hH hz
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
        have h1 := esw_norm_inv_le (specOf (Wm + A) k) hz
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
private lemma esw_res_sub {A Wm Wm' : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    (hH' : (Wm' + A).IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    GW A Wm' z - GW A Wm z = GW A Wm' z * (cplx (Wm + A) - cplx (Wm' + A)) * GW A Wm z := by
  have e : cplx (Wm + A) - cplx (Wm' + A) =
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) -
        (cplx (Wm' + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) := by abel
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, esw_mul_GW hH hz, Matrix.mul_one,
    esw_GW_mul hH' hz, Matrix.one_mul]

/-- The first resolvent identity `G(z') − G(z) = (z' − z) G(z') G(z)`. -/
private lemma esw_res_sub_z {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    GW A Wm z' - GW A Wm z = (z' - z) • (GW A Wm z' * GW A Wm z) := by
  have e : (z' - z) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (cplx (Wm + A) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) -
        (cplx (Wm + A) - z' • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    rw [sub_smul]; abel
  have h : GW A Wm z' * ((z' - z) • (1 : Matrix (Fin N) (Fin N) ℂ)) * GW A Wm z =
      GW A Wm z' - GW A Wm z := by
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, esw_mul_GW hH hz, Matrix.mul_one,
      esw_GW_mul hH hz', Matrix.one_mul]
  rw [← h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- `p ↦ G^W(p)` is continuous along a continuous family of symmetric matrices and spectral
parameters in the upper half-plane. -/
private lemma esw_continuous_GW {X : Type*} [TopologicalSpace X] (A : Matrix (Fin N) (Fin N) ℝ)
    {Wf : X → Matrix (Fin N) (Fin N) ℝ} {zf : X → ℂ} (hWf : Continuous Wf) (hzf : Continuous zf)
    (hH : ∀ p, (Wf p + A).IsHermitian) (hz : ∀ p, 0 < (zf p).im) :
    Continuous fun p => GW A (Wf p) (zf p) := by
  have hM : Continuous fun p => cplx (Wf p + A) - zf p • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    have h1 : Continuous fun p => cplx (Wf p + A) :=
      ((hWf.add continuous_const).matrix_map Complex.continuous_ofReal)
    exact h1.sub (hzf.smul continuous_const)
  rw [continuous_iff_continuousAt]
  intro p
  have hu := esw_isUnit (hH p) (hz p)
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  exact hinv.comp (f := fun p => cplx (Wf p + A) - zf p • (1 : Matrix (Fin N) (Fin N) ℂ))
    hM.continuousAt

end Resolvent

/-! ## Updates of a symmetric entry -/

section Update

variable {N : ℕ}

private lemma esw_Wupd_symm {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm) (i j : Fin N)
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

private lemma esw_Wupd_herm {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) (i j : Fin N) (t : ℝ) : (Wupd Wm i j t + A).IsHermitian :=
  (esw_herm_of_symm (esw_Wupd_symm (esw_symm_of_herm hW) i j t)).add hA

private lemma esw_Wupd_self {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm) (i j : Fin N) :
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
private lemma esw_cplx_Wupd_sub (A Wm : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (t x : ℝ) :
    cplx (Wupd Wm i j t + A) - cplx (Wupd Wm i j x + A) = ((t - x : ℝ) : ℂ) • deltaW i j := by
  ext a b
  simp only [cplx, Matrix.sub_apply, Matrix.map_apply, Matrix.add_apply, Wupd, deltaW,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma esw_continuous_Wupd (i j : Fin N) :
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
private lemma esw_im_pole (lam y η : ℝ) :
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
private lemma esw_integral_pole (lam η E₁ E₂ : ℝ) (hη : 0 < η) :
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
private lemma esw_smCount_eq {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    smCount (Wm + A) η E₁ E₂ =
      Real.pi⁻¹ * ∫ y in E₁..E₂, (trace (GW A Wm ((y : ℂ) + η * Complex.I))).im := by
  have hz : ∀ y : ℝ, 0 < ((y : ℂ) + η * Complex.I).im := fun y => by simpa using hη
  have him : ∀ y : ℝ, (trace (GW A Wm ((y : ℂ) + η * Complex.I))).im =
      ∑ k, η / ((specOf (Wm + A) k - y) ^ 2 + η ^ 2) := by
    intro y
    rw [esw_trace_GW hH (hz y), Complex.im_sum]
    simp only [esw_im_pole _ y η]
  simp only [him]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [esw_integral_pole _ η E₁ E₂ hη]
    unfold smCount
    rw [← Finset.sum_div, div_eq_inv_mul]
  · intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.div (by fun_prop) fun y => by positivity

/-- Entrywise derivative of a matrix-valued function of one real variable. -/
private def EswMD {ι : Type*} (f : ℝ → Matrix ι ι ℂ) (f' : Matrix ι ι ℂ) (x : ℝ) : Prop :=
  ∀ s t, HasDerivAt (fun y => f y s t) (f' s t) x

private lemma esw_MD_mul {ι : Type*} [Fintype ι] {f g : ℝ → Matrix ι ι ℂ}
    {f' g' : Matrix ι ι ℂ} {x : ℝ} (hf : EswMD f f' x) (hg : EswMD g g' x) :
    EswMD (fun y => f y * g y) (f' * g x + f x * g') x := by
  intro s t
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun u _ => (hf s u).mul (hg u t)

private lemma esw_MD_const {ι : Type*} (C : Matrix ι ι ℂ) (x : ℝ) :
    EswMD (fun _ => C) 0 x :=
  fun s t => by simpa using hasDerivAt_const x (C s t)

private lemma esw_MD_trace {ι : Type*} [Fintype ι] {f : ℝ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ}
    {x : ℝ} (hf : EswMD f f' x) : HasDerivAt (fun y => trace (f y)) (trace f') x := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact HasDerivAt.fun_sum fun s _ => hf s s

private lemma esw_hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The entrywise derivative from a difference identity `f(x + h) − f(x) = h • D(h)` with `D`
continuous at `0`. -/
private lemma esw_MD_of_sub {ι : Type*} {f : ℝ → Matrix ι ι ℂ} {D : ℝ → Matrix ι ι ℂ} {x : ℝ}
    (hid : ∀ h : ℝ, f (x + h) - f x = (h : ℂ) • D h)
    (hc : ∀ s t, ContinuousAt (fun h => D h s t) 0) : EswMD f (D 0) x := by
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
private lemma esw_continuous_G_t {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    Continuous fun y => GW A (Wupd Wm i j y) z :=
  esw_continuous_GW A ((esw_continuous_Wupd i j).comp (continuous_const.prodMk continuous_id))
    continuous_const (fun y => esw_Wupd_herm hA hW i j y) fun _ => hz

/-- `(t, y) ↦ G^W(W^{t}_{(ij)}, y + iη)` is jointly continuous. -/
private lemma esw_continuous_G_ty {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (i j : Fin N) :
    Continuous fun p : ℝ × ℝ => GW A (Wupd Wm i j p.1) ((p.2 : ℂ) + η * Complex.I) :=
  esw_continuous_GW A ((esw_continuous_Wupd i j).comp (continuous_const.prodMk continuous_fst))
    ((Complex.continuous_ofReal.comp continuous_snd).add continuous_const)
    (fun p => esw_Wupd_herm hA hW i j p.1) fun _ => by simpa using hη

/-- `d/dt G^W(W^{t}_{(ij)}) = −G Δ G`. -/
private lemma esw_MD_G {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) :
    EswMD (fun y => GW A (Wupd Wm i j y) z)
      (-(GW A (Wupd Wm i j x) z * deltaW i j * GW A (Wupd Wm i j x) z)) x := by
  have hid : ∀ h : ℝ, GW A (Wupd Wm i j (x + h)) z - GW A (Wupd Wm i j x) z =
      (h : ℂ) • (-(GW A (Wupd Wm i j (x + h)) z * deltaW i j * GW A (Wupd Wm i j x) z)) := by
    intro h
    rw [esw_res_sub (esw_Wupd_herm hA hW i j x) (esw_Wupd_herm hA hW i j (x + h)) hz,
      esw_cplx_Wupd_sub, show x - (x + h) = -h by ring]
    simp
  have h := esw_MD_of_sub (f := fun y => GW A (Wupd Wm i j y) z) (D := fun h =>
    -(GW A (Wupd Wm i j (x + h)) z * deltaW i j * GW A (Wupd Wm i j x) z)) hid ?_
  · simpa using h
  · intro s t
    have hc : Continuous fun h : ℝ => GW A (Wupd Wm i j (x + h)) z :=
      (esw_continuous_G_t hA hW hz i j).comp (continuous_const.add continuous_id)
    have hc2 : Continuous fun h : ℝ =>
        -(GW A (Wupd Wm i j (x + h)) z * deltaW i j * GW A (Wupd Wm i j x) z) :=
      ((hc.matrix_mul continuous_const).matrix_mul continuous_const).neg
    exact ((continuous_apply_apply s t).comp hc2).continuousAt

/-- `d/dy G^W(y + iη) = G²`. -/
private lemma esw_MD_G_re {A Wm : Matrix (Fin N) (Fin N) ℝ} (hH : (Wm + A).IsHermitian)
    {η : ℝ} (hη : 0 < η) (y : ℝ) :
    EswMD (fun w : ℝ => GW A Wm ((w : ℂ) + η * Complex.I))
      (GW A Wm ((y : ℂ) + η * Complex.I) * GW A Wm ((y : ℂ) + η * Complex.I)) y := by
  have hz : ∀ w : ℝ, 0 < ((w : ℂ) + η * Complex.I).im := fun w => by simpa using hη
  have hid : ∀ h : ℝ, GW A Wm (((y + h : ℝ) : ℂ) + η * Complex.I) -
      GW A Wm ((y : ℂ) + η * Complex.I) =
      (h : ℂ) • (GW A Wm (((y + h : ℝ) : ℂ) + η * Complex.I) *
        GW A Wm ((y : ℂ) + η * Complex.I)) := by
    intro h
    rw [esw_res_sub_z hH (hz y) (hz (y + h))]
    congr 1
    push_cast
    ring
  have h := esw_MD_of_sub (f := fun w : ℝ => GW A Wm ((w : ℂ) + η * Complex.I))
    (D := fun h => GW A Wm (((y + h : ℝ) : ℂ) + η * Complex.I) *
      GW A Wm ((y : ℂ) + η * Complex.I)) hid ?_
  · simpa using h
  · intro s t
    have hc : Continuous fun h : ℝ => GW A Wm (((y + h : ℝ) : ℂ) + η * Complex.I) :=
      esw_continuous_GW A continuous_const
        ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add
          continuous_const) (fun _ => hH) fun w => hz _
    exact ((continuous_apply_apply s t).comp (hc.matrix_mul continuous_const)).continuousAt

/-- The integrand `Im tr G^W(W^{t}_{(ij)}, y + iη)` of the smoothed count. -/
private def eswF (A Wm : Matrix (Fin N) (Fin N) ℝ) (η : ℝ) (i j : Fin N) (t y : ℝ) : ℝ :=
  (trace (GW A (Wupd Wm i j t) ((y : ℂ) + η * Complex.I))).im

/-- Its derivative in the entry: `−Im tr (Δ G²)`. -/
private def eswF' (A Wm : Matrix (Fin N) (Fin N) ℝ) (η : ℝ) (i j : Fin N) (t y : ℝ) : ℝ :=
  -(trace (deltaW i j * (GW A (Wupd Wm i j t) ((y : ℂ) + η * Complex.I) *
    GW A (Wupd Wm i j t) ((y : ℂ) + η * Complex.I)))).im

private lemma esw_hasDerivAt_F {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (i j : Fin N) (x y : ℝ) :
    HasDerivAt (fun t => eswF A Wm η i j t y) (eswF' A Wm η i j x y) x := by
  have hz : 0 < ((y : ℂ) + η * Complex.I).im := by simpa using hη
  have h := esw_hasDerivAt_im (esw_MD_trace (esw_MD_G hA hW hz i j x))
  refine h.congr_deriv ?_
  simp only [eswF']
  rw [Matrix.trace_neg, Complex.neg_im, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm]

/-- The entry derivative of the smoothed count:
`∂_{W_{ij}} 𝒳_{[E₁,E₂]} = -π⁻¹ Im (tr(Δ G)(E₂ + iη) - tr(Δ G)(E₁ + iη))`, `Δ = E_{ij} + E_{ji}`
(`-(2/π) Im[G_{ij}]` off the diagonal, `-π⁻¹ Im[G_{ii}]` on it). -/
theorem hasDerivAt_smCountW {N : ℕ} {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (u : ℝ) :
    HasDerivAt (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂)
      (-(1 / Real.pi) *
        ((trace (deltaW i j * GW A (Wupd Wm i j u) (E₂ + η * Complex.I))).im -
          (trace (deltaW i j * GW A (Wupd Wm i j u) (E₁ + η * Complex.I))).im)) u := by
  have hGc := esw_continuous_G_ty hA hW hη i j
  have hFc : Continuous fun p : ℝ × ℝ => eswF A Wm η i j p.1 p.2 := by
    simp only [eswF]
    exact Complex.continuous_im.comp hGc.matrix_trace
  have hF'c : Continuous fun p : ℝ × ℝ => eswF' A Wm η i j p.1 p.2 := by
    simp only [eswF']
    exact (Complex.continuous_im.comp
      (continuous_const.matrix_mul (hGc.matrix_mul hGc)).matrix_trace).neg
  have hFy : ∀ t, Continuous fun y => eswF A Wm η i j t y := fun t => by
    have h := hFc.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id)
    exact h
  have hF'y : ∀ t, Continuous fun y => eswF' A Wm η i j t y := fun t => by
    have h := hF'c.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id)
    exact h
  obtain ⟨C, hC⟩ := ((isCompact_closedBall u 1).prod (isCompact_uIcc (a := E₁) (b := E₂))
    ).exists_bound_of_continuousOn hF'c.continuousOn
  have hdiff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := E₁) (b := E₂) (F := eswF A Wm η i j) (F' := eswF' A Wm η i j)
    (x₀ := u) (s := Metric.ball u 1)
    (bound := fun _ => C) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun t => (hFy t).aestronglyMeasurable)
    ((hFy u).intervalIntegrable _ _) (hF'y u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y hy x hx => by
      have := hC (x, y) ⟨Metric.ball_subset_closedBall hx, Set.uIoc_subset_uIcc hy⟩
      simpa using this)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun y _ x _ => esw_hasDerivAt_F hA hW hη i j x y)
  have hHu := esw_Wupd_herm hA hW i j u
  have hg' : Continuous fun y : ℝ =>
      (trace (deltaW i j * (GW A (Wupd Wm i j u) ((y : ℂ) + η * Complex.I) *
        GW A (Wupd Wm i j u) ((y : ℂ) + η * Complex.I)))).im := by
    have h := hGc.comp (Continuous.prodMk (continuous_const (y := u)) continuous_id)
    have h' : Continuous fun y : ℝ => GW A (Wupd Wm i j u) ((y : ℂ) + η * Complex.I) := h
    exact Complex.continuous_im.comp (continuous_const.matrix_mul (h'.matrix_mul h')).matrix_trace
  have hFTC : ∫ y in E₁..E₂, eswF' A Wm η i j u y =
      -((trace (deltaW i j * GW A (Wupd Wm i j u) ((E₂ : ℂ) + η * Complex.I))).im -
        (trace (deltaW i j * GW A (Wupd Wm i j u) ((E₁ : ℂ) + η * Complex.I))).im) := by
    have hd : ∀ y ∈ Set.uIcc E₁ E₂, HasDerivAt
        (fun w : ℝ => (trace (deltaW i j * GW A (Wupd Wm i j u) ((w : ℂ) + η * Complex.I))).im)
        ((trace (deltaW i j * (GW A (Wupd Wm i j u) ((y : ℂ) + η * Complex.I) *
          GW A (Wupd Wm i j u) ((y : ℂ) + η * Complex.I)))).im) y := by
      intro y _
      have h1 := esw_MD_mul (esw_MD_const (deltaW i j) y) (esw_MD_G_re hHu hη y)
      simp only [Matrix.zero_mul, zero_add] at h1
      exact esw_hasDerivAt_im (esw_MD_trace h1)
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg'.intervalIntegrable _ _)
    simp only [eswF']
    rw [intervalIntegral.integral_neg, hint]
  have hform : (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) =
      fun t => Real.pi⁻¹ * ∫ y in E₁..E₂, eswF A Wm η i j t y := by
    funext t
    exact esw_smCount_eq (esw_Wupd_herm hA hW i j t) hη E₁ E₂
  rw [hform]
  have h := hdiff.2.const_mul Real.pi⁻¹
  rw [hFTC] at h
  convert h using 1
  ring

end Derivative

/-! ## The higher entry derivatives -/

section Higher

variable {N : ℕ}

/-- `d/dt (Δ G)^k = -k (Δ G)^{k+1}`. -/
private lemma esw_MD_pow {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (x : ℝ) (k : ℕ) :
    EswMD (fun y => (deltaW i j * GW A (Wupd Wm i j y) z) ^ k)
      (-(k : ℂ) • (deltaW i j * GW A (Wupd Wm i j x) z) ^ (k + 1)) x := by
  induction k with
  | zero => simpa using esw_MD_const (1 : Matrix (Fin N) (Fin N) ℂ) x
  | succ k ih =>
    have hDG := esw_MD_mul (esw_MD_const (deltaW i j) x) (esw_MD_G hA hW hz i j x)
    have h := esw_MD_mul ih hDG
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
private def eswPsi (A Wm : Matrix (Fin N) (Fin N) ℝ) (η E₁ E₂ : ℝ) (i j : Fin N) (k : ℕ)
    (t : ℝ) : ℝ :=
  -(1 / Real.pi) * (((-1 : ℝ) ^ k * (k.factorial : ℝ)) *
    ((trace ((deltaW i j * GW A (Wupd Wm i j t) ((E₂ : ℂ) + η * Complex.I)) ^ (k + 1))).im -
      (trace ((deltaW i j * GW A (Wupd Wm i j t) ((E₁ : ℂ) + η * Complex.I)) ^ (k + 1))).im))

private lemma esw_hasDerivAt_psi {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (k : ℕ) (x : ℝ) :
    HasDerivAt (eswPsi A Wm η E₁ E₂ i j k) (eswPsi A Wm η E₁ E₂ i j (k + 1) x) x := by
  have hb : 0 < ((E₂ : ℂ) + η * Complex.I).im := by simpa using hη
  have ha : 0 < ((E₁ : ℂ) + η * Complex.I).im := by simpa using hη
  have h2 := esw_hasDerivAt_im (esw_MD_trace (esw_MD_pow hA hW hb i j x (k + 1)))
  have h1 := esw_hasDerivAt_im (esw_MD_trace (esw_MD_pow hA hW ha i j x (k + 1)))
  have h := (h2.sub h1).const_mul (-(1 / Real.pi) * ((-1 : ℝ) ^ k * (k.factorial : ℝ)))
  unfold eswPsi
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

private lemma esw_hasDerivAt_smCount_psi {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (x : ℝ) :
    HasDerivAt (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂)
      (eswPsi A Wm η E₁ E₂ i j 0 x) x := by
  refine (hasDerivAt_smCountW hA hW hη E₁ E₂ i j x).congr_deriv ?_
  simp [eswPsi]

private lemma esw_iteratedDeriv_eq_psi {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (n : ℕ) :
    iteratedDeriv (n + 1) (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) =
      eswPsi A Wm η E₁ E₂ i j n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext x
    exact (esw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (esw_hasDerivAt_psi hA hW hη E₁ E₂ i j n x).deriv

/-- The smoothed count is smooth in a symmetric entry. -/
private lemma esw_contDiff_smCount {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (n : ℕ) :
    ContDiff ℝ n (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) := by
  have hP : ∀ m : ℕ, ∀ k : ℕ, ContDiff ℝ m (eswPsi A Wm η E₁ E₂ i j k) := by
    intro m
    induction m with
    | zero =>
      intro k
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
        (esw_hasDerivAt_psi hA hW hη E₁ E₂ i j k x).continuousAt)
    | succ m ih =>
      intro k
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun x => (esw_hasDerivAt_psi hA hW hη E₁ E₂ i j k x).differentiableAt,
        fun h => absurd h (by simp), ?_⟩
      have : deriv (eswPsi A Wm η E₁ E₂ i j k) = eswPsi A Wm η E₁ E₂ i j (k + 1) :=
        funext fun x => (esw_hasDerivAt_psi hA hW hη E₁ E₂ i j k x).deriv
      rw [this]
      exact ih (k + 1)
  cases n with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (esw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).continuousAt)
  | succ m =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (esw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have : deriv (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) = eswPsi A Wm η E₁ E₂ i j 0 :=
      funext fun x => (esw_hasDerivAt_smCount_psi hA hW hη E₁ E₂ i j x).deriv
    rw [this]
    exact hP m 0

end Higher

/-! ## The `2 × 2` block of `tr (Δ G)^k` and bounds on the entry derivatives -/

section Block

variable {N : ℕ}

/-- The pattern of `Δ` on `(i, j)`: `[[0, 1], [1, 0]]` off the diagonal, `[[1, 0], [0, 0]]` on
it. -/
private def eswD (i j : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = j then !![1, 0; 0, 0] else !![0, 1; 1, 0]

/-- The `2 × 2` block governing `tr (Δ B)^k`. -/
private def eswBlk (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  eswD i j * !![B i i, B i j; B j i, B j j]

/-- `tr (Δ B)^{k+1}` is the trace of the `(k+1)`-st power of the `2 × 2` block. -/
private lemma esw_trace_delta_pow (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (k : ℕ) :
    trace ((deltaW i j * B) ^ (k + 1)) = trace ((eswBlk B i j) ^ (k + 1)) := by
  set ι : Fin 2 → Fin N := ![i, j] with hι
  set P : Matrix (Fin N) (Fin 2) ℂ := Matrix.of fun s r => if s = ι r then 1 else 0 with hP
  set R : Matrix (Fin 2) (Fin N) ℂ := eswD i j * Pᵀ * B with hR
  have hPBP : Pᵀ * B * P = !![B i i, B i j; B j i, B j j] := by
    ext r c
    have e : (Pᵀ * B * P) r c = B (ι r) (ι c) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, hP, Matrix.transpose_apply, Matrix.of_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_one,
        mul_zero]
    rw [e]
    fin_cases r <;> fin_cases c <;> simp [hι]
  have hΔ : deltaW i j = P * eswD i j * Pᵀ := by
    ext s u
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP, Matrix.of_apply, Matrix.transpose_apply,
      eswD, deltaW, hι]
    by_cases hij : i = j
    · subst hij
      by_cases hs : s = i <;> by_cases hu : u = i <;> simp [hs, hu]
    · by_cases hs : s = i <;> by_cases hu : u = j <;> by_cases hs' : s = j <;>
        by_cases hu' : u = i <;> simp_all
  have h1 : deltaW i j * B = P * R := by
    rw [hΔ, hR]; simp only [Matrix.mul_assoc]
  have h2 : R * P = eswBlk B i j := by
    rw [hR, eswBlk, ← hPBP]; simp only [Matrix.mul_assoc]
  have h3 : ∀ k : ℕ, (P * R) ^ (k + 1) = P * ((R * P) ^ k * R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h1, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ, h2]

private lemma esw_blk_sub (B B' : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    eswBlk B i j - eswBlk B' i j = eswBlk (B - B') i j := by
  simp only [eswBlk, ← Matrix.mul_sub]
  congr 1
  ext r c
  fin_cases r <;> fin_cases c <;> simp

/-- The entries of the block are entries of `B` on `{i, j}²` or zero. -/
private lemma esw_blk_le (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) {W : ℝ} (hW0 : 0 ≤ W)
    (h1 : ‖B i i‖ ≤ W) (h2 : ‖B i j‖ ≤ W) (h3 : ‖B j i‖ ≤ W) (h4 : ‖B j j‖ ≤ W) (r c : Fin 2) :
    ‖eswBlk B i j r c‖ ≤ W := by
  unfold eswBlk eswD
  split_ifs <;> fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> assumption

private lemma esw_entry_mul_le (X Y : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℝ}
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

private lemma esw_pow_entry_le (X : Matrix (Fin 2) (Fin 2) ℂ) {a : ℝ}
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
    refine (esw_entry_mul_le _ _ ih hX r c).trans (le_of_eq ?_)
    ring

private lemma esw_pow_sub_entry_le (X Y : Matrix (Fin 2) (Fin 2) ℂ) {a δ : ℝ}
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
    have t1 := esw_entry_mul_le _ _ (esw_pow_entry_le X hX k) hXY r c
    have t2 := esw_entry_mul_le _ _ ih hY r c
    refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans (le_of_eq ?_))
    push_cast
    ring

private lemma esw_trace_two_le (X : Matrix (Fin 2) (Fin 2) ℂ) {a : ℝ}
    (hX : ∀ r c, ‖X r c‖ ≤ a) : ‖trace X‖ ≤ 2 * a := by
  rw [Matrix.trace_fin_two]
  calc ‖X 0 0 + X 1 1‖ ≤ ‖X 0 0‖ + ‖X 1 1‖ := norm_add_le _ _
    _ ≤ 2 * a := by linarith [hX 0 0, hX 1 1]

private lemma esw_factorial_le {n : ℕ} (hn : n ≤ 4) : (n.factorial : ℝ) ≤ 24 := by
  have : n.factorial ≤ 24 := by interval_cases n <;> decide
  exact_mod_cast this

/-- `|-(1/π) (-1)^n n! (Im a - Im b)| ≤ 24 ‖a - b‖` for `n ≤ 4`. -/
private lemma esw_coef_le {n : ℕ} (hn : n ≤ 4) (a b : ℂ) :
    |-(1 / Real.pi) * (((-1 : ℝ) ^ n * (n.factorial : ℝ)) * (a.im - b.im))| ≤ 24 * ‖a - b‖ := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : |a.im - b.im| ≤ ‖a - b‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi), Nat.abs_cast]
  have hf := esw_factorial_le hn
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hp : 1 / Real.pi ≤ 1 := by rw [div_le_one (by positivity)]; exact hpi
  calc 1 / Real.pi * ((n.factorial : ℝ) * |a.im - b.im|) ≤ 1 * (24 * ‖a - b‖) := by
        gcongr
    _ = 24 * ‖a - b‖ := one_mul _

/-- Entry bounds `|G_{st}| ≤ W` on `{i, j}²` at both window points give
`|∂^{n+1} 𝒳| ≤ (192 W)^{n+1}` for `n + 1 ≤ 5`. -/
private lemma esw_deriv_le_crude {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hW : Wm.IsHermitian) {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) (i j : Fin N) (s : ℝ) {Wb : ℝ}
    (hWb : 0 ≤ Wb)
    (h₁ : ∀ a b, ‖GW A (Wupd Wm i j s) ((E₁ : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    (h₂ : ∀ a b, ‖GW A (Wupd Wm i j s) ((E₂ : ℂ) + η * Complex.I) a b‖ ≤ Wb)
    {n : ℕ} (hn : n ≤ 4) :
    |iteratedDeriv (n + 1) (fun t => smCount (Wupd Wm i j t + A) η E₁ E₂) s| ≤
      (192 * Wb) ^ (n + 1) := by
  rw [esw_iteratedDeriv_eq_psi hA hW hη E₁ E₂ i j n]
  unfold eswPsi
  refine (esw_coef_le hn _ _).trans ?_
  rw [esw_trace_delta_pow, esw_trace_delta_pow]
  have b2 := esw_pow_entry_le _ (esw_blk_le _ i j hWb (h₂ _ _) (h₂ _ _) (h₂ _ _) (h₂ _ _)) n
  have b1 := esw_pow_entry_le _ (esw_blk_le _ i j hWb (h₁ _ _) (h₁ _ _) (h₁ _ _) (h₁ _ _)) n
  have t2 := esw_trace_two_le _ b2
  have t1 := esw_trace_two_le _ b1
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
private lemma esw_deriv_le_small {A Wm : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
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
  rw [esw_iteratedDeriv_eq_psi hA hW hη E₁ E₂ i j n]
  unfold eswPsi
  refine (esw_coef_le hn _ _).trans ?_
  rw [esw_trace_delta_pow, esw_trace_delta_pow, ← Matrix.trace_sub]
  set B₂ := GW A (Wupd Wm i j s) ((E₂ : ℂ) + η * Complex.I)
  set B₁ := GW A (Wupd Wm i j s) ((E₁ : ℂ) + η * Complex.I)
  have hb2 := esw_blk_le B₂ i j (by linarith) (h₂ i hi i hi) (h₂ i hi j hj) (h₂ j hj i hi)
    (h₂ j hj j hj)
  have hb1 := esw_blk_le B₁ i j (by linarith) (h₁ i hi i hi) (h₁ i hi j hj) (h₁ j hj i hi)
    (h₁ j hj j hj)
  have hbd : ∀ r c, ‖(eswBlk B₂ i j - eswBlk B₁ i j) r c‖ ≤ δ := by
    rw [esw_blk_sub]
    exact esw_blk_le _ i j hδ (by simpa using hd i hi i hi) (by simpa using hd i hi j hj)
      (by simpa using hd j hj i hi) (by simpa using hd j hj j hj)
  have he := esw_pow_sub_entry_le _ _ hb2 hb1 hbd n
  have ht := esw_trace_two_le _ he
  have hp : (2 * Wb) ^ n ≤ (2 * Wb) ^ 4 := pow_le_pow_right₀ (by linarith) hn
  have hn' : ((n : ℝ) + 1) ≤ 5 := by exact_mod_cast (show n + 1 ≤ 5 by omega)
  have h0 : 0 ≤ (2 * Wb) ^ n := by positivity
  calc 24 * ‖trace ((eswBlk B₂ i j) ^ (n + 1) - (eswBlk B₁ i j) ^ (n + 1))‖
      ≤ 24 * (2 * (2 * (n + 1) * (2 * Wb) ^ n * δ)) := by gcongr
    _ = 96 * ((n + 1) * (2 * Wb) ^ n) * δ := by ring
    _ ≤ 96 * (5 * (2 * Wb) ^ 4) * δ := by gcongr
    _ = 480 * (2 * Wb) ^ 4 * δ := by ring

end Block

/-! ## Taylor expansion, moments and the probabilistic part of the swaps -/

section Prob

/-- Iterated derivatives of a vector-valued function are taken componentwise. -/
private lemma esw_iteratedDeriv_pi {l : ℕ} (φ : ℝ → Fin l → ℝ)
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

/-- Faà di Bruno bound: if `‖D^m F‖ ≤ C_b` for `m ≤ 5` and the `i`-th derivatives of the
components of `φ` at `t` are at most `D^i` for `1 ≤ i ≤ n ≤ 5`, then
`|(F ∘ φ)^{(n)}(t)| ≤ n! C_b D^n`. -/
private lemma esw_comp_le {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn : n ≤ 5) (t : ℝ)
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ D ^ i) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * D ^ n := by
  have hφc : ContDiff ℝ 5 φ := contDiff_pi.2 fun j => hφ j 5
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine norm_iteratedFDeriv_comp_le hF hφc (by exact_mod_cast hn) t
    (fun i hi => hFb i (hi.trans hn) _) fun i h1 h2 => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, esw_iteratedDeriv_pi φ hφ]
  exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    rw [Real.norm_eq_abs]; exact hD i h1 h2 j

/-- The same bound with one small factor: if the component derivatives of orders `1, …, n` at
`t` are at most `Θ ∈ [0, 1]`, then `|(F ∘ φ)^{(n)}(t)| ≤ n! C_b Θ`. -/
private lemma esw_comp_le_small {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) (φ : ℝ → Fin l → ℝ)
    (hφ : ∀ (j : Fin l) (n : ℕ), ContDiff ℝ n fun t => φ t j) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 5)
    (t : ℝ) {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ j, |iteratedDeriv i (fun s => φ s j) t| ≤ Θ) :
    |iteratedDeriv n (F ∘ φ) t| ≤ n.factorial * Cb * Θ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set D : ℝ := Θ ^ ((n : ℝ)⁻¹) with hDdef
  have hD0 : 0 ≤ D := Real.rpow_nonneg hΘ0 _
  have hDn : D ^ n = Θ := by
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0, inv_mul_cancel₀ hn0.ne', Real.rpow_one]
  have h := esw_comp_le hF hFb φ hφ hn t hD0 fun i h1 h2 j => by
    refine (hD i h1 h2 j).trans ?_
    rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul hΘ0]
    conv_lhs => rw [← Real.rpow_one Θ]
    refine Real.rpow_le_rpow_of_exponent_ge' hΘ0 hΘ1 (by positivity) ?_
    rw [inv_mul_le_iff₀ hn0, mul_one]
    exact_mod_cast h2
  rwa [hDn] at h

/-- Taylor's formula at `0` with the Lagrange remainder, the intermediate point bounded by `|y|`. -/
private lemma esw_taylor (h : ℝ → ℝ) (n : ℕ) (hh : ContDiff ℝ (n + 1) h) (y : ℝ) :
    ∃ ξ, |ξ| ≤ |y| ∧ h y = ∑ k ∈ Finset.range (n + 1), iteratedDeriv k h 0 * y ^ k / k.factorial +
      iteratedDeriv (n + 1) h ξ * y ^ (n + 1) / (n + 1).factorial := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨0, by simp, ?_⟩
    rw [Finset.sum_range_succ']
    simp
  · obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hy) hh.contDiffOn
    refine ⟨x', ?_, ?_⟩
    · rw [Set.uIoo, Set.mem_Ioo] at hx'
      rcases le_total 0 y with h0 | h0
      · rw [min_eq_left h0, max_eq_right h0] at hx'
        rw [abs_of_pos hx'.1, abs_of_nonneg h0]; exact hx'.2.le
      · rw [min_eq_right h0, max_eq_left h0] at hx'
        rw [abs_of_neg hx'.2, abs_of_nonpos h0]; linarith [hx'.1]
    · rw [taylor_within_apply, sub_zero] at heq
      have hk : ∀ k ∈ Finset.range (n + 1),
          ((k.factorial : ℝ)⁻¹ * y ^ k) • iteratedDerivWithin k h (Set.uIcc 0 y) 0 =
            iteratedDeriv k h 0 * y ^ k / k.factorial := by
        intro k hk
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hy))
          (hh.contDiffAt.of_le (by
            have := Finset.mem_range.1 hk
            exact_mod_cast Nat.le_succ_of_le (Nat.lt_succ_iff.1 this))) Set.left_mem_uIcc,
          smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl hk] at heq
      linarith

/-- Measurability of the iterated derivatives in a parameter, from the joint measurability of
the function and its smoothness in the variable. -/
private lemma esw_measurable_iteratedDeriv {α : Type*} [MeasurableSpace α] (φ : α → ℝ → ℝ)
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

/-- `|y|^k = N^{-k/2} |√N y|^k`. -/
private lemma esw_abs_pow_eq {N : ℕ} (hN : 1 ≤ N) (y : ℝ) (k : ℕ) :
    |y| ^ k = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * y| ^ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← mul_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn.le,
    ← Real.rpow_add hn]
  have : -(k : ℝ) / 2 + 1 / 2 * k = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-- Integrability of `y^k` from that of `|√N y|^k`. -/
private lemma esw_integrable_pow {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {y : Ω → ℝ} (hy : Measurable y) {k : ℕ}
    (hi : Integrable fun ω => |Real.sqrt N * y ω| ^ k) : Integrable fun ω => y ω ^ k := by
  refine (hi.const_mul ((N : ℝ) ^ (-(k : ℝ) / 2))).mono' (hy.pow_const k).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow, esw_abs_pow_eq hN]

/-- `|E y^k| ≤ N^{-k/2} C_k` when `E |√N y|^k ≤ C_k`. -/
private lemma esw_abs_integral_pow_le {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    {y : Ω → ℝ} {k : ℕ} {Ck : ℝ}
    (hi : Integrable fun ω => |Real.sqrt N * y ω| ^ k)
    (hC : ∫ ω, |Real.sqrt N * y ω| ^ k ≤ Ck) :
    |∫ ω, y ω ^ k| ≤ (N : ℝ) ^ (-(k : ℝ) / 2) * Ck := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hi.const_mul ((N : ℝ) ^ (-(k : ℝ) / 2)))
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_pow, esw_abs_pow_eq hN]
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hC (by positivity)

/-- The integral of a function bounded by `a |y|^k` on a good set and by `b |y|^k` off it, where
off the good set either `T ≥ 1` or `|√N y| > N^ε`:
`|E r| ≤ a N^{-k/2} C_k + b (N^{-k/2-pε} C_{k+p} + N^{-k/2+kε} β)` when `E T ≤ β`. -/
private lemma esw_split_integral {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (C : ℕ → ℝ) {y : Ω → ℝ}
    (hmom : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (k p : ℕ) {T : Ω → ℝ} (hT : Integrable T) (hT0 : ∀ ω, 0 ≤ T ω) {β : ℝ}
    (hβ : ∫ ω, T ω ≤ β) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : Ω → ℝ)
    (hr : ∀ ω, |r ω| ≤ a * |y ω| ^ k ∨
      (|r ω| ≤ b * |y ω| ^ k ∧ (1 ≤ T ω ∨ (N : ℝ) ^ ε < |Real.sqrt N * y ω|))) :
    |∫ ω, r ω| ≤ a * ((N : ℝ) ^ (-(k : ℝ) / 2) * C k) +
      b * ((N : ℝ) ^ (-(k : ℝ) / 2 - p * ε) * C (k + p) +
        (N : ℝ) ^ (-(k : ℝ) / 2 + k * ε) * β) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set c1 : ℝ := (N : ℝ) ^ (-(k : ℝ) / 2) with hc1
  set c2 : ℝ := (N : ℝ) ^ (-(k : ℝ) / 2 - p * ε) with hc2
  set c3 : ℝ := (N : ℝ) ^ (-(k : ℝ) / 2 + k * ε) with hc3
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by positivity
  set g : Ω → ℝ := fun ω => a * (c1 * |Real.sqrt N * y ω| ^ k) +
    b * (c2 * |Real.sqrt N * y ω| ^ (k + p) + c3 * T ω) with hg
  have hgi : Integrable g :=
    (((hmom k).1.const_mul c1).const_mul a).add
      ((((hmom (k + p)).1.const_mul c2).add (hT.const_mul c3)).const_mul b)
  have hpt : ∀ ω, |r ω| ≤ g ω := by
    intro ω
    have hw0 : 0 ≤ |Real.sqrt N * y ω| := abs_nonneg _
    have hyk : |y ω| ^ k = c1 * |Real.sqrt N * y ω| ^ k := esw_abs_pow_eq hN _ k
    have hA : 0 ≤ a * (c1 * |Real.sqrt N * y ω| ^ k) := by positivity
    have hB2 : 0 ≤ b * (c2 * |Real.sqrt N * y ω| ^ (k + p)) := by positivity
    have hB3 : 0 ≤ b * (c3 * T ω) := mul_nonneg hb (mul_nonneg hc30 (hT0 ω))
    rcases hr ω with h | ⟨h, hT1 | hbig⟩
    · rw [hyk] at h
      simp only [hg]
      nlinarith
    · by_cases hbig : (N : ℝ) ^ ε < |Real.sqrt N * y ω|
      · have hp : (N : ℝ) ^ (p * ε) ≤ |Real.sqrt N * y ω| ^ p := by
          rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
          exact pow_le_pow_left₀ (by positivity) hbig.le p
        have hc12 : c1 = c2 * (N : ℝ) ^ (p * ε) := by
          rw [hc1, hc2, ← Real.rpow_add hn]; congr 1; ring
        have : |y ω| ^ k ≤ c2 * |Real.sqrt N * y ω| ^ (k + p) := by
          rw [hyk, hc12, pow_add]
          have := mul_le_mul_of_nonneg_left hp (mul_nonneg hc20 (pow_nonneg hw0 k))
          nlinarith
        simp only [hg]
        nlinarith [mul_le_mul_of_nonneg_left this hb]
      · push Not at hbig
        have hk : |Real.sqrt N * y ω| ^ k ≤ (N : ℝ) ^ (k * ε) := by
          have e : (N : ℝ) ^ ((k : ℝ) * ε) = ((N : ℝ) ^ ε) ^ k := by
            rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
          rw [e]
          exact pow_le_pow_left₀ hw0 hbig k
        have hc13 : c1 * (N : ℝ) ^ (k * ε) = c3 := by
          rw [hc1, hc3, ← Real.rpow_add hn]
        have : |y ω| ^ k ≤ c3 * T ω := by
          rw [hyk]
          calc c1 * |Real.sqrt N * y ω| ^ k ≤ c1 * (N : ℝ) ^ (k * ε) :=
                mul_le_mul_of_nonneg_left hk hc10
            _ = c3 * 1 := by rw [hc13, mul_one]
            _ ≤ c3 * T ω := mul_le_mul_of_nonneg_left hT1 hc30
        simp only [hg]
        nlinarith [mul_le_mul_of_nonneg_left this hb]
    · have hp : (N : ℝ) ^ (p * ε) ≤ |Real.sqrt N * y ω| ^ p := by
        rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) hbig.le p
      have hc12 : c1 = c2 * (N : ℝ) ^ (p * ε) := by
        rw [hc1, hc2, ← Real.rpow_add hn]; congr 1; ring
      have : |y ω| ^ k ≤ c2 * |Real.sqrt N * y ω| ^ (k + p) := by
        rw [hyk, hc12, pow_add]
        have := mul_le_mul_of_nonneg_left hp (mul_nonneg hc20 (pow_nonneg hw0 k))
        nlinarith
      simp only [hg]
      nlinarith [mul_le_mul_of_nonneg_left this hb]
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hpt ω
  · have i1 : Integrable fun ω => a * (c1 * |Real.sqrt N * y ω| ^ k) :=
      ((hmom k).1.const_mul c1).const_mul a
    have i2 : Integrable fun ω => c2 * |Real.sqrt N * y ω| ^ (k + p) :=
      (hmom (k + p)).1.const_mul c2
    have i3 : Integrable fun ω => c3 * T ω := hT.const_mul c3
    have i23 : Integrable fun ω => c2 * |Real.sqrt N * y ω| ^ (k + p) + c3 * T ω := i2.add i3
    have e : ∫ ω, g ω = a * (c1 * ∫ ω, |Real.sqrt N * y ω| ^ k) +
        b * ((c2 * ∫ ω, |Real.sqrt N * y ω| ^ (k + p)) + c3 * ∫ ω, T ω) := by
      simp only [hg]
      rw [integral_add i1 (i23.const_mul b), integral_const_mul, integral_const_mul,
        integral_const_mul, integral_add i2 i3, integral_const_mul, integral_const_mul]
    rw [e]
    gcongr
    · exact (hmom k).2
    · exact (hmom (k + p)).2

/-- The Taylor expansion of `E f(X, y)` at `y = 0` to order three, for `y` independent of `X`
with `E y = 0` and `E y² = 1/N`: the remainder is
`f(X, y) - ∑_{k ≤ 3} ∂^k f(X, 0) y^k / k!`. -/
private lemma esw_expand {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [MeasurableSpace α] {N : ℕ} (hN : 1 ≤ N) (f : α → ℝ → ℝ)
    (hΦ : ∀ n ≤ 3, Measurable fun p : α × ℝ => iteratedDeriv n (f p.1) p.2) {B : ℝ}
    (hB : ∀ n ≤ 3, ∀ a s, |iteratedDeriv n (f a) s| ≤ B) {X : Ω → α} (hX : Measurable X)
    {y : Ω → ℝ} (hy : Measurable y) (hind : IndepFun X y) (h1 : ∫ ω, y ω = 0)
    (h2 : ∫ ω, y ω ^ 2 = 1 / (N : ℝ))
    (hmom : ∀ q : ℕ, Integrable fun ω => |Real.sqrt N * y ω| ^ q) :
    ∫ ω, f (X ω) (y ω) = (∫ ω, f (X ω) 0) +
      1 / (N : ℝ) / 2 * (∫ ω, iteratedDeriv 2 (f (X ω)) 0) +
      (∫ ω, y ω ^ 3) / 6 * (∫ ω, iteratedDeriv 3 (f (X ω)) 0) +
      ∫ ω, (f (X ω) (y ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
        iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 +
          iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6)) := by
  have hm : ∀ n ≤ 3, Measurable fun ω => iteratedDeriv n (f (X ω)) 0 := fun n hn =>
    (hΦ n hn).comp (hX.prodMk measurable_const)
  have hbd : ∀ n ≤ 3, ∀ᵐ ω ∂(ℙ : Measure Ω), ‖iteratedDeriv n (f (X ω)) 0‖ ≤ B := fun n hn =>
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB n hn _ _
  have hyk : ∀ k : ℕ, Integrable fun ω => y ω ^ k := fun k =>
    esw_integrable_pow hN hy (hmom k)
  have hg : ∀ n ≤ 3, Integrable fun ω => iteratedDeriv n (f (X ω)) 0 * y ω ^ n := fun n hn =>
    (hyk n).bdd_mul (hm n hn).aestronglyMeasurable (hbd n hn)
  have hint : ∀ n ≤ 3, ∫ ω, iteratedDeriv n (f (X ω)) 0 * y ω ^ n =
      (∫ ω, iteratedDeriv n (f (X ω)) 0) * ∫ ω, y ω ^ n := by
    intro n hn
    have hi := hind.comp (φ := fun a => iteratedDeriv n (f a) 0) (ψ := fun t => t ^ n)
      ((hΦ n hn).comp (measurable_id.prodMk measurable_const)) (measurable_id.pow_const n)
    exact hi.integral_fun_mul_eq_mul_integral (hm n hn).aestronglyMeasurable
      ((hy.pow_const n).aestronglyMeasurable)
  have hf0 : Measurable fun ω => f (X ω) (y ω) := by
    have := (hΦ 0 (by norm_num)).comp (hX.prodMk hy)
    simpa [Function.comp_def] using this
  have hfi : Integrable fun ω => f (X ω) (y ω) :=
    Integrable.of_bound hf0.aestronglyMeasurable B (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; simpa using hB 0 (by norm_num) (X ω) (y ω))
  have hg0 : Integrable fun ω => f (X ω) 0 := by
    have := hg 0 (by norm_num); simpa using this
  have hg1 := hg 1 (by norm_num)
  have hg2 := (hg 2 (by norm_num)).div_const 2
  have hg3 := (hg 3 (by norm_num)).div_const 6
  simp only [pow_one] at hg1
  have hS : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
      iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y ω ^ 3 / 6 :=
    ((hg0.add hg1).add hg2).add hg3
  have hA : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω := hg0.add hg1
  have hA2 : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω +
      iteratedDeriv 2 (f (X ω)) 0 * y ω ^ 2 / 2 := hA.add hg2
  rw [integral_sub hfi hS, integral_add hA2 hg3, integral_add hA hg2, integral_add hg0 hg1,
    integral_div, integral_div]
  have i1 := hint 1 (by norm_num)
  have i2 := hint 2 (by norm_num)
  have i3 := hint 3 (by norm_num)
  simp only [pow_one] at i1
  rw [i1, i2, i3, h1, h2]
  ring

/-- `c N^y ≤ 1/2` eventually, for `y < 0`. -/
private lemma esw_ev_small {y : ℝ} (hy : y < 0) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ y ≤ 1 / 2 := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ y) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -y) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun N : ℕ => c * (N : ℝ) ^ y) atTop (𝓝 0) := by
    simpa using h1.const_mul c
  exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le

/-- `N^x ≤ N^y` for `x ≤ y`, `N ≥ 1`. -/
private lemma esw_rpow_le {N : ℕ} (hN : 1 ≤ N) {x y : ℝ} (h : x ≤ y) :
    (N : ℝ) ^ x ≤ (N : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

private lemma esw_iteratedDeriv_iteratedDeriv (g : ℝ → ℝ) (a b : ℕ) :
    iteratedDeriv a (iteratedDeriv b g) = iteratedDeriv (a + b) g := by
  simp only [iteratedDeriv_eq_iterate]
  funext x
  rw [Function.iterate_add_apply]

/-- `|√N z| ≤ N^ε` gives `|z| ≤ N^{-1/2+ε}`. -/
private lemma esw_abs_le_of_sqrt {N : ℕ} (hN : 1 ≤ N) {ε z : ℝ}
    (h : |Real.sqrt N * z| ≤ (N : ℝ) ^ ε) : |z| ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  rw [abs_mul, abs_of_pos hs] at h
  have e : (N : ℝ) ^ (-1 / 2 + ε) = (N : ℝ) ^ ε / Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn]; congr 1; ring
  rw [e, le_div_iff₀ hs, mul_comm]
  exact h

/-- `|√N z|^p N^{-pε} ≥ 1` when `|√N z| > N^ε`. -/
private lemma esw_markov_one {N : ℕ} (hN : 1 ≤ N) {ε z : ℝ} (p : ℕ)
    (h : (N : ℝ) ^ ε < |Real.sqrt N * z|) :
    1 ≤ |Real.sqrt N * z| ^ p * (N : ℝ) ^ (-((p : ℝ) * ε)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ ((p : ℝ) * ε) ≤ |Real.sqrt N * z| ^ p := by
    have e : (N : ℝ) ^ ((p : ℝ) * ε) = ((N : ℝ) ^ ε) ^ p := by
      rw [mul_comm, Real.rpow_mul hn.le, Real.rpow_natCast]
    rw [e]
    exact pow_le_pow_left₀ (by positivity) h.le p
  rw [Real.rpow_neg hn.le]
  have hpos : 0 < (N : ℝ) ^ ((p : ℝ) * ε) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact hp

/-- Moving the order-three coefficient from the entry value `0` to `x_α(X)`: with
`E[∂⁴f(X, 0) x_α] = 0`, `E ∂³f(X, x_α) = E ∂³f(X, 0) + E R'`, where `|R'| ≤ 60 C_b x_α²` on the
good event and `|R'| ≤ 60 C_b D⁵ x_α²` everywhere. -/
private lemma esw_coef {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [MeasurableSpace α] {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (C : ℕ → ℝ) (p : ℕ) (f : α → ℝ → ℝ)
    (hfc : ∀ a, ContDiff ℝ 5 (f a))
    (hΦ : ∀ n ≤ 5, Measurable fun q : α × ℝ => iteratedDeriv n (f q.1) q.2)
    {Cb D β : ℝ} (hCb : 0 ≤ Cb) (hD : 0 ≤ D) (Good : α → Prop) (xα : α → ℝ)
    (hcrude : ∀ n ≤ 5, ∀ a s, |iteratedDeriv n (f a) s| ≤ n.factorial * Cb * D ^ n)
    (hgood : ∀ a s, Good a → |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 5 (f a) s| ≤ 120 * Cb)
    {X : Ω → α} (hX : Measurable X) (hxα : Measurable fun ω => xα (X ω))
    (hind : IndepFun (fun ω => iteratedDeriv 4 (f (X ω)) 0) (fun ω => xα (X ω)))
    (hmean : ∫ ω, xα (X ω) = 0)
    (hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * xα (X ω)| ^ q) ∧
      ∫ ω, |Real.sqrt N * xα (X ω)| ^ q ≤ C q)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTX1 : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) :
    ∫ ω, iteratedDeriv 3 (f (X ω)) (xα (X ω)) = (∫ ω, iteratedDeriv 3 (f (X ω)) 0) +
        ∫ ω, (iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
          iteratedDeriv 4 (f (X ω)) 0 * xα (X ω)) ∧
      |∫ ω, (iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
          iteratedDeriv 4 (f (X ω)) 0 * xα (X ω))| ≤
        60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * C 2) +
          60 * Cb * D ^ 5 * ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * C (2 + p) +
            (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * β) := by
  have hbd : ∀ n ≤ 5, ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ s, ‖iteratedDeriv n (f (X ω)) s‖ ≤
      n.factorial * Cb * D ^ n := fun n hn =>
    Eventually.of_forall fun ω s => by rw [Real.norm_eq_abs]; exact hcrude n hn _ _
  have hm3a : Measurable fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) := by
    have h := (hΦ 3 (by norm_num)).comp (hX.prodMk hxα)
    exact h
  have hm30 : Measurable fun ω => iteratedDeriv 3 (f (X ω)) 0 := by
    have h := (hΦ 3 (by norm_num)).comp (hX.prodMk (measurable_const (a := (0 : ℝ))))
    exact h
  have hm40 : Measurable fun ω => iteratedDeriv 4 (f (X ω)) 0 := by
    have h := (hΦ 4 (by norm_num)).comp (hX.prodMk (measurable_const (a := (0 : ℝ))))
    exact h
  have hi3a : Integrable fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) :=
    Integrable.of_bound hm3a.aestronglyMeasurable _
      ((hbd 3 (by norm_num)).mono fun ω h => h _)
  have hi30 : Integrable fun ω => iteratedDeriv 3 (f (X ω)) 0 :=
    Integrable.of_bound hm30.aestronglyMeasurable _
      ((hbd 3 (by norm_num)).mono fun ω h => h _)
  have hxi : Integrable fun ω => xα (X ω) := by
    have := esw_integrable_pow hN hxα (k := 1) (hmomX 1).1
    simpa using this
  have hi4 : Integrable fun ω => iteratedDeriv 4 (f (X ω)) 0 * xα (X ω) :=
    hxi.bdd_mul hm40.aestronglyMeasurable ((hbd 4 (by norm_num)).mono fun ω h => h _)
  have h40 : ∫ ω, iteratedDeriv 4 (f (X ω)) 0 * xα (X ω) = 0 := by
    rw [hind.integral_fun_mul_eq_mul_integral hm40.aestronglyMeasurable hxα.aestronglyMeasurable]
    change (∫ ω, iteratedDeriv 4 (f (X ω)) 0) * ∫ ω, xα (X ω) = 0
    rw [hmean, mul_zero]
  refine ⟨?_, ?_⟩
  · have h' : Integrable fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) -
        iteratedDeriv 3 (f (X ω)) 0 := hi3a.sub hi30
    rw [integral_sub h' hi4, integral_sub hi3a hi30, h40]
    ring
  · refine (esw_split_integral hN (ε := ε) C hmomX 2 p hTXi hTX0 hTXint (a := 60 * Cb)
      (b := 60 * Cb * D ^ 5) (by positivity) (by positivity)
      (fun ω => iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
        iteratedDeriv 4 (f (X ω)) 0 * xα (X ω)) fun ω => ?_).trans (le_of_eq ?_)
    · have hc2 : ContDiff ℝ 2 (iteratedDeriv 3 (f (X ω))) := by
        rw [iteratedDeriv_eq_iterate]
        exact ContDiff.iterate_deriv' 2 3 (by simpa using hfc (X ω))
      obtain ⟨ξ, hξ, heq⟩ := esw_taylor (iteratedDeriv 3 (f (X ω))) 1 (hc2.of_le (by norm_num))
        (xα (X ω))
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
        Nat.factorial, Nat.cast_one, div_one, mul_one, esw_iteratedDeriv_iteratedDeriv] at heq
      have hr : iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
          iteratedDeriv 4 (f (X ω)) 0 * xα (X ω) =
          iteratedDeriv 5 (f (X ω)) ξ * xα (X ω) ^ 2 / 2 := by
        rw [heq]; push_cast; ring_nf
      rw [hr, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      by_cases hg : Good (X ω) ∧ |Real.sqrt N * xα (X ω)| ≤ (N : ℝ) ^ ε
      · left
        have hs := esw_abs_le_of_sqrt hN hg.2
        have hb := hgood (X ω) ξ hg.1 hs (hξ.trans hs)
        calc |iteratedDeriv 5 (f (X ω)) ξ| * |xα (X ω)| ^ 2 / 2
            ≤ 120 * Cb * |xα (X ω)| ^ 2 / 2 := by
              gcongr
          _ = 60 * Cb * |xα (X ω)| ^ 2 := by ring
      · right
        refine ⟨?_, ?_⟩
        · have hc := hcrude 5 le_rfl (X ω) ξ
          calc |iteratedDeriv 5 (f (X ω)) ξ| * |xα (X ω)| ^ 2 / 2 ≤
                (Nat.factorial 5 : ℝ) * Cb * D ^ 5 * |xα (X ω)| ^ 2 / 2 := by gcongr
            _ = 60 * Cb * D ^ 5 * |xα (X ω)| ^ 2 := by norm_num [Nat.factorial]; ring
        · by_cases h1 : Good (X ω)
          · right
            push Not at hg
            exact hg h1
          · left
            rcases hTX1 ω with h | h
            · exact absurd h h1
            · exact h
    · push_cast
      ring

/-- `|a - b - (m₁ - m₀)/6 · d| ≤ |a| + |b| + (|m₁| + |m₀|)/6 · |d|`. -/
private lemma esw_abs_combine (a b m₁ m₀ d : ℝ) :
    |a - b - (m₁ - m₀) / 6 * d| ≤ |a| + |b| + (|m₁| + |m₀|) / 6 * |d| := by
  have h1 : |(m₁ - m₀) / 6 * d| ≤ (|m₁| + |m₀|) / 6 * |d| := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    gcongr
    exact abs_sub _ _
  calc |a - b - (m₁ - m₀) / 6 * d| ≤ |a - b| + |(m₁ - m₀) / 6 * d| := abs_sub _ _
    _ ≤ |a| + |b| + (|m₁| + |m₀|) / 6 * |d| := by linarith [abs_sub a b]

/-- The Taylor remainder at order `n + 1` of `E f(X, y)`: on the good event (`X` good,
`|√N x_α(X)|, |√N y| ≤ N^ε`) `|∂^{n+1} f| ≤ (n+1)! C_b Θ`, and everywhere
`|∂^{n+1} f| ≤ (n+1)! C_b D^{n+1}`. -/
private lemma esw_remainder {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (C : ℕ → ℝ) (p n : ℕ) (f : α → ℝ → ℝ)
    (hfc : ∀ a, ContDiff ℝ (n + 1) (f a)) {Cb D Θ β : ℝ} (hCb : 0 ≤ Cb) (hD0 : 0 ≤ D)
    (hΘ : 0 ≤ Θ) (Good : α → Prop) (xα : α → ℝ)
    (hcrude : ∀ a s, |iteratedDeriv (n + 1) (f a) s| ≤ (n + 1).factorial * Cb * D ^ (n + 1))
    (hgood : ∀ a s, Good a → |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv (n + 1) (f a) s| ≤ (n + 1).factorial * Cb * Θ)
    (X : Ω → α) {y : Ω → ℝ}
    (hmom : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y ω| ^ q ≤ C q)
    (hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * xα (X ω)| ^ q) ∧
      ∫ ω, |Real.sqrt N * xα (X ω)| ^ q ≤ C q)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTX1 : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) :
    |∫ ω, (f (X ω) (y ω) - ∑ k ∈ Finset.range (n + 1),
        iteratedDeriv k (f (X ω)) 0 * y ω ^ k / k.factorial)| ≤
      Cb * Θ * ((N : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 2) * C (n + 1)) +
        Cb * D ^ (n + 1) * ((N : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 2 - p * ε) * C (n + 1 + p) +
          (N : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 2 + ((n + 1 : ℕ) : ℝ) * ε) *
            (β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p)) := by
  have hfac : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  set T : Ω → ℝ := fun ω => TX ω + |Real.sqrt N * xα (X ω)| ^ p * (N : ℝ) ^ (-((p : ℝ) * ε))
    with hT
  have hTi : Integrable T := hTXi.add ((hmomX p).1.mul_const _)
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => add_nonneg (hTX0 ω) (by positivity)
  have hTint : ∫ ω, T ω ≤ β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p := by
    simp only [hT]
    rw [integral_add hTXi ((hmomX p).1.mul_const _), integral_mul_const]
    have hpos : 0 ≤ (N : ℝ) ^ (-((p : ℝ) * ε)) := by positivity
    nlinarith [(hmomX p).2]
  have h := esw_split_integral hN (ε := ε) C hmom (n + 1) p hTi hT0 hTint (a := Cb * Θ)
    (b := Cb * D ^ (n + 1)) (by positivity) (by positivity)
    (fun ω => f (X ω) (y ω) - ∑ k ∈ Finset.range (n + 1),
      iteratedDeriv k (f (X ω)) 0 * y ω ^ k / k.factorial) fun ω => ?_
  · exact h
  obtain ⟨ξ, hξ, heq⟩ := esw_taylor (f (X ω)) n (hfc (X ω)) (y ω)
  have hr : f (X ω) (y ω) - ∑ k ∈ Finset.range (n + 1),
      iteratedDeriv k (f (X ω)) 0 * y ω ^ k / k.factorial =
      iteratedDeriv (n + 1) (f (X ω)) ξ * y ω ^ (n + 1) / (n + 1).factorial := by
    rw [heq]; ring
  rw [hr, abs_div, abs_mul, abs_pow, abs_of_pos hfac]
  have hy4 : 0 ≤ |y ω| ^ (n + 1) := by positivity
  by_cases hg : Good (X ω) ∧ |Real.sqrt N * xα (X ω)| ≤ (N : ℝ) ^ ε ∧
      |Real.sqrt N * y ω| ≤ (N : ℝ) ^ ε
  · left
    have hb := hgood (X ω) ξ hg.1 (esw_abs_le_of_sqrt hN hg.2.1)
      (hξ.trans (esw_abs_le_of_sqrt hN hg.2.2))
    calc |iteratedDeriv (n + 1) (f (X ω)) ξ| * |y ω| ^ (n + 1) / (n + 1).factorial
        ≤ (n + 1).factorial * Cb * Θ * |y ω| ^ (n + 1) / (n + 1).factorial := by
          gcongr
      _ = Cb * Θ * |y ω| ^ (n + 1) := by field_simp
  · right
    refine ⟨?_, ?_⟩
    · calc |iteratedDeriv (n + 1) (f (X ω)) ξ| * |y ω| ^ (n + 1) / (n + 1).factorial
          ≤ (n + 1).factorial * Cb * D ^ (n + 1) * |y ω| ^ (n + 1) / (n + 1).factorial := by
            gcongr
            exact hcrude _ _
        _ = Cb * D ^ (n + 1) * |y ω| ^ (n + 1) := by field_simp
    · by_cases h1 : Good (X ω)
      · by_cases h2 : |Real.sqrt N * xα (X ω)| ≤ (N : ℝ) ^ ε
        · right
          push Not at hg
          exact hg h1 h2
        · left
          push Not at h2
          have := esw_markov_one hN p h2
          simp only [hT]
          linarith [hTX0 ω]
      · left
        rcases hTX1 ω with h | h
        · exact absurd h h1
        · simp only [hT]
          have : 0 ≤ |Real.sqrt N * xα (X ω)| ^ p * (N : ℝ) ^ (-((p : ℝ) * ε)) := by positivity
          linarith

/-- Union bound for finitely many events of probability `≥ 1 - q`: a nonnegative integrable
`T` with `E T ≤ |ι| q` such that at every point either all events hold or `T ≥ 1`. -/
private lemma esw_events {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
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

/-- The probabilistic part of the off-diagonal swap: for `f(X, t)` with the deterministic bound
`|∂ⁿ f| ≤ n! C_b Dⁿ` and the bound `|∂ⁿ f| ≤ n! C_b Θ` on a good set of `X` near `x_α(X) = 0`,
whose complement is controlled by `T ≥ 1` with `E T ≤ β`, the difference of the two swaps minus
the third-moment term is bounded by the remainder, tail and coefficient-move terms. -/
private lemma esw_prob_off {Ω α : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [MeasurableSpace α] {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (C : ℕ → ℝ) (p : ℕ) {X : Ω → α}
    (hXm : Measurable X) (xα : α → ℝ) (hxα : Measurable fun ω => xα (X ω))
    (hmean : ∫ ω, xα (X ω) = 0)
    (hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * xα (X ω)| ^ q) ∧
      ∫ ω, |Real.sqrt N * xα (X ω)| ^ q ≤ C q)
    (f : α → ℝ → ℝ) (hfc : ∀ a, ContDiff ℝ 5 (f a))
    (hΦ : ∀ n ≤ 5, Measurable fun q : α × ℝ => iteratedDeriv n (f q.1) q.2)
    (hind : IndepFun (fun ω => iteratedDeriv 4 (f (X ω)) 0) (fun ω => xα (X ω)))
    {Cb D Θ β : ℝ} (hCb : 0 ≤ Cb) (hD1 : 1 ≤ D) (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ 1) (Good : α → Prop)
    (hcrude : ∀ n ≤ 5, ∀ (a : α) (s : ℝ), |iteratedDeriv n (f a) s| ≤ n.factorial * Cb * D ^ n)
    (hgood : ∀ (a : α) (s : ℝ), Good a → |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      ∀ n : ℕ, 1 ≤ n → n ≤ 5 → |iteratedDeriv n (f a) s| ≤ n.factorial * Cb * Θ)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTXg : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) {y₁ y₀ : Ω → ℝ} (hi₁ : IndepFun X y₁)
    (hi₀ : IndepFun X y₀) (hy₁ : Measurable y₁) (hy₀ : Measurable y₀) (hE₁ : ∫ ω, y₁ ω = 0)
    (hE₀ : ∫ ω, y₀ ω = 0) (hV₁ : ∫ ω, y₁ ω ^ 2 = 1 / (N : ℝ))
    (hV₀ : ∫ ω, y₀ ω ^ 2 = 1 / (N : ℝ))
    (hM₁ : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y₁ ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y₁ ω| ^ q ≤ C q)
    (hM₀ : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y₀ ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y₀ ω| ^ q ≤ C q) :
    |((∫ ω, f (X ω) (y₁ ω)) - (∫ ω, f (X ω) (y₀ ω))) -
        ((∫ ω, y₁ ω ^ 3) - (∫ ω, y₀ ω ^ 3)) / 6 *
          (∫ ω, iteratedDeriv 3 (f (X ω)) (xα (X ω)))| ≤
      2 * (Cb * Θ * ((N : ℝ) ^ (-(4 : ℝ) / 2) * C 4) +
        Cb * D ^ 4 * ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * C (4 + p) +
          (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p))) +
      2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * C 3) / 6 *
        (60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * C 2) +
          60 * Cb * D ^ 5 * ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * C (2 + p) +
            (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * β)) := by
  have hD0 : 0 ≤ D := by linarith
  have hB3 : ∀ n ≤ 3, ∀ (a : α) (s : ℝ), |iteratedDeriv n (f a) s| ≤ 6 * Cb * D ^ 3 := by
    intro n hn a s
    refine (hcrude n (by omega) a s).trans ?_
    have hfac : (n.factorial : ℝ) ≤ 6 := by
      have : n.factorial ≤ 6 := by interval_cases n <;> decide
      exact_mod_cast this
    have hpow : D ^ n ≤ D ^ 3 := pow_le_pow_right₀ hD1 hn
    have h0 : 0 ≤ D ^ n := by positivity
    calc (n.factorial : ℝ) * Cb * D ^ n ≤ 6 * Cb * D ^ n := by gcongr
      _ ≤ 6 * Cb * D ^ 3 := by gcongr
  have e₁ := esw_expand hN f (fun n hn => hΦ n (by omega)) hB3 hXm hy₁ hi₁ hE₁ hV₁
    (fun q => (hM₁ q).1)
  have e₀ := esw_expand hN f (fun n hn => hΦ n (by omega)) hB3 hXm hy₀ hi₀ hE₀ hV₀
    (fun q => (hM₀ q).1)
  have hcrude4 : ∀ (a : α) (s : ℝ),
      |iteratedDeriv (3 + 1) (f a) s| ≤ (3 + 1).factorial * Cb * D ^ (3 + 1) :=
    fun a s => hcrude 4 (by norm_num) a s
  have hgood4 : ∀ (a : α) (s : ℝ), Good a →
      |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv (3 + 1) (f a) s| ≤ (3 + 1).factorial * Cb * Θ :=
    fun a s hG hXs hs => hgood a s hG hXs hs 4 (by norm_num) (by norm_num)
  have hgood5 : ∀ (a : α) (s : ℝ), Good a →
      |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 5 (f a) s| ≤ 120 * Cb := by
    intro a s hG hXs hs
    have h := hgood a s hG hXs hs 5 (by norm_num) (by norm_num)
    norm_num [Nat.factorial] at h
    nlinarith
  have hfc4 : ∀ a, ContDiff ℝ (3 + 1) (f a) := fun a => (hfc a).of_le (by norm_num)
  have r₁ := esw_remainder hN (ε := ε) C p 3 f hfc4 hCb hD0 hΘ0 Good xα hcrude4
    hgood4 X hM₁ hmomX hTX0 hTXi hTXint hTXg
  have r₀ := esw_remainder hN (ε := ε) C p 3 f hfc4 hCb hD0 hΘ0 Good xα hcrude4
    hgood4 X hM₀ hmomX hTX0 hTXi hTXint hTXg
  have hsum : ∀ (ω : Ω) (y : ℝ), ∑ k ∈ Finset.range (3 + 1),
      iteratedDeriv k (f (X ω)) 0 * y ^ k / k.factorial =
      f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y + iteratedDeriv 2 (f (X ω)) 0 * y ^ 2 / 2 +
        iteratedDeriv 3 (f (X ω)) 0 * y ^ 3 / 6 := by
    intro ω y
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      iteratedDeriv_zero, Nat.factorial, Nat.cast_one, div_one, mul_one]
    push_cast
    ring
  simp only [hsum] at r₁ r₀
  have hc := esw_coef hN (ε := ε) C p f hfc hΦ hCb hD0 Good xα
    hcrude hgood5 hXm hxα hind hmean hmomX hTX0 hTXi hTXint hTXg
  rw [e₁, e₀, hc.1]
  have m₁ := esw_abs_integral_pow_le hN (hM₁ 3).1 (hM₁ 3).2
  have m₀ := esw_abs_integral_pow_le hN (hM₀ 3).1 (hM₀ 3).2
  push_cast at m₁ m₀ r₁ r₀
  generalize ∫ ω, (f (X ω) (y₁ ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y₁ ω +
    iteratedDeriv 2 (f (X ω)) 0 * y₁ ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y₁ ω ^ 3 / 6)) = a₁
    at r₁ ⊢
  generalize ∫ ω, (f (X ω) (y₀ ω) - (f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y₀ ω +
    iteratedDeriv 2 (f (X ω)) 0 * y₀ ω ^ 2 / 2 + iteratedDeriv 3 (f (X ω)) 0 * y₀ ω ^ 3 / 6)) = a₀
    at r₀ ⊢
  generalize ∫ ω, (iteratedDeriv 3 (f (X ω)) (xα (X ω)) - iteratedDeriv 3 (f (X ω)) 0 -
    iteratedDeriv 4 (f (X ω)) 0 * xα (X ω)) = d at hc ⊢
  generalize ∫ ω, y₁ ω ^ 3 = u₁ at m₁ ⊢
  generalize ∫ ω, y₀ ω ^ 3 = u₀ at m₀ ⊢
  generalize ∫ ω, f (X ω) 0 = v₀
  generalize ∫ ω, iteratedDeriv 2 (f (X ω)) 0 = v₂
  generalize ∫ ω, iteratedDeriv 3 (f (X ω)) 0 = v₃
  have key : v₀ + 1 / (N : ℝ) / 2 * v₂ + u₁ / 6 * v₃ + a₁ -
      (v₀ + 1 / (N : ℝ) / 2 * v₂ + u₀ / 6 * v₃ + a₀) - (u₁ - u₀) / 6 * (v₃ + d) =
      a₁ - a₀ - (u₁ - u₀) / 6 * d := by ring
  rw [key]
  refine (esw_abs_combine _ _ _ _ _).trans ?_
  have hm3 : (|u₁| + |u₀|) / 6 ≤ 2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * C 3) / 6 := by linarith
  have hd0 : 0 ≤ |d| := abs_nonneg _
  have hm30 : 0 ≤ 2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * C 3) / 6 := by
    have hC3 : 0 ≤ C 3 := (integral_nonneg fun ω => by positivity).trans (hM₁ 3).2
    positivity
  have hprod := mul_le_mul hm3 hc.2 hd0 hm30
  norm_num at r₁ r₀ ⊢
  linarith

/-- The probabilistic part of the diagonal swap: for `y₁`, `y₀` independent of `X` with mean
`0`, `|E f(X, y₁) − E f(X, y₀)|` is bounded by twice the order-two remainder. -/
private lemma esw_prob_diag {Ω α : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] [MeasurableSpace α] {N : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (C : ℕ → ℝ) (p : ℕ) {X : Ω → α} (hXm : Measurable X) (xα : α → ℝ)
    (hmomX : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * xα (X ω)| ^ q) ∧
      ∫ ω, |Real.sqrt N * xα (X ω)| ^ q ≤ C q)
    (f : α → ℝ → ℝ) (hfc : ∀ a, ContDiff ℝ 2 (f a))
    (hΦ : ∀ n ≤ 2, Measurable fun q : α × ℝ => iteratedDeriv n (f q.1) q.2)
    {Cb D Θ β : ℝ} (hCb : 0 ≤ Cb) (hD0 : 0 ≤ D) (hΘ0 : 0 ≤ Θ) (Good : α → Prop)
    (hcrude : ∀ n ≤ 2, ∀ (a : α) (s : ℝ), |iteratedDeriv n (f a) s| ≤ n.factorial * Cb * D ^ n)
    (hgood : ∀ (a : α) (s : ℝ), Good a → |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |iteratedDeriv 2 (f a) s| ≤ 2 * Cb * Θ)
    {TX : Ω → ℝ} (hTX0 : ∀ ω, 0 ≤ TX ω) (hTXi : Integrable TX) (hTXint : ∫ ω, TX ω ≤ β)
    (hTXg : ∀ ω, Good (X ω) ∨ 1 ≤ TX ω) {y₁ y₀ : Ω → ℝ} (hi₁ : IndepFun X y₁)
    (hi₀ : IndepFun X y₀) (hy₁ : Measurable y₁) (hy₀ : Measurable y₀) (hE₁ : ∫ ω, y₁ ω = 0)
    (hE₀ : ∫ ω, y₀ ω = 0)
    (hM₁ : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y₁ ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y₁ ω| ^ q ≤ C q)
    (hM₀ : ∀ q : ℕ, Integrable (fun ω => |Real.sqrt N * y₀ ω| ^ q) ∧
      ∫ ω, |Real.sqrt N * y₀ ω| ^ q ≤ C q) :
    |(∫ ω, f (X ω) (y₁ ω)) - (∫ ω, f (X ω) (y₀ ω))| ≤
      2 * (Cb * Θ * ((N : ℝ) ^ (-(2 : ℝ) / 2) * C 2) +
        Cb * D ^ 2 * ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * C (2 + p) +
          (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (β + (N : ℝ) ^ (-((p : ℝ) * ε)) * C p))) := by
  have hB1 : ∀ n ≤ 1, ∀ (a : α) (s : ℝ), |iteratedDeriv n (f a) s| ≤ Cb * (1 + D) := by
    intro n hn a s
    refine (hcrude n (by omega) a s).trans ?_
    interval_cases n
    · simp only [Nat.factorial, Nat.cast_one, pow_zero, mul_one, one_mul]
      nlinarith
    · simp only [Nat.factorial, Nat.cast_one, pow_one, one_mul, mul_one]
      nlinarith
  have hexp : ∀ {y : Ω → ℝ}, Measurable y → IndepFun X y → ∫ ω, y ω = 0 →
      (∀ q : ℕ, Integrable fun ω => |Real.sqrt N * y ω| ^ q) →
      ∫ ω, f (X ω) (y ω) = (∫ ω, f (X ω) 0) +
        ∫ ω, (f (X ω) (y ω) - ∑ k ∈ Finset.range (1 + 1),
          iteratedDeriv k (f (X ω)) 0 * y ω ^ k / k.factorial) := by
    intro y hy hind h1 hmom
    have hm : ∀ n ≤ 1, Measurable fun ω => iteratedDeriv n (f (X ω)) 0 := fun n hn =>
      (hΦ n (by omega)).comp (hXm.prodMk measurable_const)
    have hbd : ∀ n ≤ 1, ∀ᵐ ω ∂(ℙ : Measure Ω), ‖iteratedDeriv n (f (X ω)) 0‖ ≤ Cb * (1 + D) :=
      fun n hn => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB1 n hn _ _
    have hy1 : Integrable fun ω => y ω := by
      have := esw_integrable_pow hN hy (k := 1) (hmom 1)
      simpa using this
    have hg1 : Integrable fun ω => iteratedDeriv 1 (f (X ω)) 0 * y ω :=
      hy1.bdd_mul (hm 1 le_rfl).aestronglyMeasurable (hbd 1 le_rfl)
    have hint1 : ∫ ω, iteratedDeriv 1 (f (X ω)) 0 * y ω = 0 := by
      have hi := hind.comp (φ := fun a => iteratedDeriv 1 (f a) 0) (ψ := id)
        ((hΦ 1 (by norm_num)).comp (measurable_id.prodMk measurable_const)) measurable_id
      have := hi.integral_fun_mul_eq_mul_integral (hm 1 le_rfl).aestronglyMeasurable
        hy.aestronglyMeasurable
      change ∫ ω, iteratedDeriv 1 (f (X ω)) 0 * y ω =
        (∫ ω, iteratedDeriv 1 (f (X ω)) 0) * ∫ ω, y ω at this
      rw [this, h1, mul_zero]
    have hf0 : Measurable fun ω => f (X ω) (y ω) := by
      have := (hΦ 0 (by norm_num)).comp (hXm.prodMk hy)
      simpa [Function.comp_def] using this
    have hfi : Integrable fun ω => f (X ω) (y ω) :=
      Integrable.of_bound hf0.aestronglyMeasurable (Cb * (1 + D)) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; simpa using hB1 0 (by norm_num) (X ω) (y ω))
    have hg0 : Integrable fun ω => f (X ω) 0 :=
      Integrable.of_bound ((hm 0 (by norm_num)).aestronglyMeasurable.congr
        (Eventually.of_forall fun ω => by simp)) (Cb * (1 + D)) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; simpa using hB1 0 (by norm_num) (X ω) 0)
    have hs : ∀ ω, ∑ k ∈ Finset.range (1 + 1), iteratedDeriv k (f (X ω)) 0 * y ω ^ k /
        k.factorial = f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω := by
      intro ω
      simp [Finset.sum_range_succ]
    have hS : Integrable fun ω => f (X ω) 0 + iteratedDeriv 1 (f (X ω)) 0 * y ω := hg0.add hg1
    simp only [hs]
    rw [integral_sub hfi hS, integral_add hg0 hg1, hint1]
    ring
  have hfc2 : ∀ a, ContDiff ℝ (1 + 1) (f a) := hfc
  have hcrude2 : ∀ (a : α) (s : ℝ),
      |iteratedDeriv (1 + 1) (f a) s| ≤ (1 + 1).factorial * Cb * D ^ (1 + 1) :=
    fun a s => hcrude 2 le_rfl a s
  have hgood2 : ∀ (a : α) (s : ℝ), Good a →
      |xα a| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv (1 + 1) (f a) s| ≤ (1 + 1).factorial * Cb * Θ := by
    intro a s hG hXs hs
    have h := hgood a s hG hXs hs
    simpa [Nat.factorial] using h
  have r₁ := esw_remainder hN (ε := ε) C p 1 f hfc2 hCb hD0 hΘ0 Good xα hcrude2
    hgood2 X hM₁ hmomX hTX0 hTXi hTXint hTXg
  have r₀ := esw_remainder hN (ε := ε) C p 1 f hfc2 hCb hD0 hΘ0 Good xα hcrude2
    hgood2 X hM₀ hmomX hTX0 hTXi hTXint hTXg
  rw [hexp hy₁ hi₁ hE₁ (fun q => (hM₁ q).1), hexp hy₀ hi₀ hE₀ (fun q => (hM₀ q).1)]
  push_cast at r₁ r₀
  have e : ∀ a b c : ℝ, c + a - (c + b) = a - b := fun a b c => by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  norm_num at r₁ r₀ ⊢
  linarith

end Prob

/-! ## The entry function of a Wigner matrix and its bounds -/

section WignerEntry

variable {N : ℕ}

/-- The symmetric matrix read off the upper triangle of `W`. -/
private def eswSym (Wm : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun s u => if s ≤ u then Wm s u else Wm u s

private lemma esw_sym_symm (Wm : Matrix (Fin N) (Fin N) ℝ) : (eswSym Wm)ᵀ = eswSym Wm := by
  ext s u
  simp only [Matrix.transpose_apply, eswSym]
  rcases lt_trichotomy s u with h | rfl | h
  · simp [not_le.2 h, h.le]
  · rfl
  · simp [not_le.2 h, h.le]

private lemma esw_sym_herm (Wm : Matrix (Fin N) (Fin N) ℝ) : (eswSym Wm).IsHermitian :=
  esw_herm_of_symm (esw_sym_symm Wm)

private lemma esw_sym_eq {Wm : Matrix (Fin N) (Fin N) ℝ} (hW : Wmᵀ = Wm) : eswSym Wm = Wm := by
  ext s u
  simp only [eswSym]
  split_ifs
  · rfl
  · have := congrFun (congrFun hW s) u
    simpa [Matrix.transpose_apply] using this

private lemma esw_sym_apply (Wm : Matrix (Fin N) (Fin N) ℝ) {i j : Fin N} (hij : i ≤ j) :
    eswSym Wm i j = Wm i j := by
  simp [eswSym, hij]

private lemma esw_continuous_sym : Continuous fun Wm : Matrix (Fin N) (Fin N) ℝ => eswSym Wm := by
  refine continuous_matrix fun s u => ?_
  by_cases h : s ≤ u
  · simpa [eswSym, h] using continuous_id.matrix_elem s u
  · simpa [eswSym, h] using continuous_id.matrix_elem u s

private lemma esw_Wupd_sym_Wupd (Wm : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c t : ℝ) :
    Wupd (eswSym (Wupd Wm i j c)) i j t = Wupd (eswSym Wm) i j t := by
  funext a b
  by_cases h : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
  · simp [Wupd, h]
  · have h' : ¬((b = i ∧ a = j) ∨ (b = j ∧ a = i)) := by tauto
    simp only [Wupd, h, eswSym]
    split_ifs <;> simp_all

/-- The function `t ↦ F(𝒳(W^{t}_{(ij)} + A))` of the entry `(i, j)`, `W` read off its upper
triangle. -/
private def eswf {l : ℕ} (F : (Fin l → ℝ) → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) (Wm : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) : ℝ :=
  smFW F A (Wupd (eswSym Wm) i j t) η Ea Eb

private lemma esw_f_Wupd {l : ℕ} (F : (Fin l → ℝ) → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) (Wm : Matrix (Fin N) (Fin N) ℝ) :
    eswf F A η Ea Eb i j (Wupd Wm i j 0) = eswf F A η Ea Eb i j Wm := by
  funext t
  simp only [eswf, esw_Wupd_sym_Wupd]

private lemma esw_f_contDiff {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) (Wm : Matrix (Fin N) (Fin N) ℝ) :
    ContDiff ℝ 5 (eswf F A η Ea Eb i j Wm) :=
  hF.comp (contDiff_pi.2 fun k =>
    esw_contDiff_smCount hA (esw_sym_herm Wm) hη (Ea k) (Eb k) i j 5)

private lemma esw_f_continuous {l : ℕ} {F : (Fin l → ℝ) → ℝ} (hF : ContDiff ℝ 5 F)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η)
    (Ea Eb : Fin l → ℝ) (i j : Fin N) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => eswf F A η Ea Eb i j q.1 q.2 := by
  have hW : Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ => Wupd (eswSym q.1) i j q.2 :=
    (esw_continuous_Wupd i j).comp ((esw_continuous_sym.comp continuous_fst).prodMk
      continuous_snd)
  have hc : ∀ E₁ E₂ : ℝ, Continuous fun q : Matrix (Fin N) (Fin N) ℝ × ℝ =>
      smCount (Wupd (eswSym q.1) i j q.2 + A) η E₁ E₂ := by
    intro E₁ E₂
    have he : (fun q : Matrix (Fin N) (Fin N) ℝ × ℝ =>
        smCount (Wupd (eswSym q.1) i j q.2 + A) η E₁ E₂) = fun q => Real.pi⁻¹ *
          ∫ y in E₁..E₂,
            (trace (GW A (Wupd (eswSym q.1) i j q.2) ((y : ℂ) + η * Complex.I))).im := by
      funext q
      exact esw_smCount_eq (esw_Wupd_herm hA (esw_sym_herm q.1) i j q.2) hη E₁ E₂
    rw [he]
    refine continuous_const.mul ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : Matrix (Fin N) (Fin N) ℝ × ℝ) (y : ℝ) =>
        (trace (GW A (Wupd (eswSym q.1) i j q.2) ((y : ℂ) + η * Complex.I))).im) ?_ E₁ E₂
    have hG := esw_continuous_GW A (Wf := fun p : (Matrix (Fin N) (Fin N) ℝ × ℝ) × ℝ =>
        Wupd (eswSym p.1.1) i j p.1.2)
      (zf := fun p : (Matrix (Fin N) (Fin N) ℝ × ℝ) × ℝ => ((p.2 : ℝ) : ℂ) + η * Complex.I)
      (hW.comp continuous_fst)
      ((Complex.continuous_ofReal.comp continuous_snd).add continuous_const)
      (fun p : (Matrix (Fin N) (Fin N) ℝ × ℝ) × ℝ =>
        esw_Wupd_herm hA (esw_sym_herm p.1.1) i j p.1.2) fun _ => by simpa using hη
    exact Complex.continuous_im.comp hG.matrix_trace
  exact hF.continuous.comp (continuous_pi fun k => hc (Ea k) (Eb k))

/-- An entry of a matrix is at most its operator norm. -/
private lemma esw_entry_le_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (s t : ι) : ‖A s t‖ ≤ ‖A‖ := by
  have h1 := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (Pi.single t (1 : ℂ)))
  have h2 : ‖(WithLp.toLp 2 (Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι)‖ = 1 := by
    simp
  have h3 : ‖A s t‖ ≤ ‖(WithLp.toLp 2 (A *ᵥ Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι)‖ := by
    have := PiLp.norm_apply_le (WithLp.toLp 2 (A *ᵥ Pi.single t (1 : ℂ)) : EuclideanSpace ℂ ι) s
    simpa [mulVec_single_one] using this
  rw [h2, mul_one] at h1
  exact h3.trans h1

private lemma esw_testBilin_single (B : Matrix (Fin N) (Fin N) ℂ) (s t : Fin N) :
    testBilin (Pi.single s 1) B (Pi.single t 1) = B s t := by
  simp only [testBilin, dotProduct, mulVec, Pi.single_apply]
  simp [apply_ite, ite_mul, Finset.sum_ite_eq']

private lemma esw_testNorm_single (s : Fin N) : testNorm (Pi.single s (1 : ℝ)) = 1 := by
  simp [testNorm, Pi.single_apply]

/-- `‖(P Δ Q)_{ab}‖ ≤ ‖P_{ai}‖ ‖Q_{jb}‖ + ‖P_{aj}‖ ‖Q_{ib}‖`. -/
private lemma esw_mul_delta_mul_le (P Q : Matrix (Fin N) (Fin N) ℂ) (i j a b : Fin N) :
    ‖(P * deltaW i j * Q) a b‖ ≤ ‖P a i‖ * ‖Q j b‖ + ‖P a j‖ * ‖Q i b‖ := by
  by_cases hij : i = j
  · subst hij
    have e : (P * deltaW i i * Q) a b = P a i * Q i b := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [deltaW]
        · intro c _ hc; simp [deltaW, hc]
        · simp
      · intro c _ hc
        rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
        intro e _
        simp [deltaW, hc]
      · simp
    rw [e, norm_mul]
    have := mul_nonneg (norm_nonneg (P a i)) (norm_nonneg (Q i b))
    linarith
  · have hPD : ∀ c, (P * deltaW i j) a c = (if c = j then P a i else 0) +
        (if c = i then P a j else 0) := by
      intro c
      rw [Matrix.mul_apply]
      by_cases hcj : c = j
      · subst hcj
        have hji : c ≠ i := Ne.symm hij
        rw [Finset.sum_eq_single i]
        · simp [deltaW, hji]
        · intro e _ he; simp [deltaW, he, hji]
        · simp
      · by_cases hci : c = i
        · subst hci
          rw [Finset.sum_eq_single j]
          · simp [deltaW, hcj]
          · intro e _ he; simp [deltaW, he, hcj]
          · simp
        · rw [Finset.sum_eq_zero]
          · simp [hcj, hci]
          · intro e _; simp [deltaW, hcj, hci]
    have e : (P * deltaW i j * Q) a b = P a i * Q j b + P a j * Q i b := by
      rw [Matrix.mul_apply]
      simp only [hPD, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]

/-- Stability of the entries on `{i, j}²` under a change `d` of the entry `(i, j)`: from
`|G_{ab}| ≤ M` and `2dM ≤ 1/2`, `|G'_{ab} − G_{ab}| ≤ 4 d M²` and `|G'_{ab}| ≤ 2M`. -/
private lemma esw_stab {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (hB : Bᵀ = B)
    {z : ℂ} (hz : 0 < z.im) (i j : Fin N) (s : ℝ) {M d : ℝ}
    (hM : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)), ‖GW A B z a b‖ ≤ M)
    (hd : |B i j - s| ≤ d) (hdM : 2 * d * M ≤ 1 / 2) :
    ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (Wupd B i j s) z a b - GW A B z a b‖ ≤ 4 * d * M ^ 2 ∧
        ‖GW A (Wupd B i j s) z a b‖ ≤ 2 * M := by
  have hi : i ∈ ({i, j} : Set (Fin N)) := Set.mem_insert _ _
  have hj : j ∈ ({i, j} : Set (Fin N)) := Set.mem_insert_of_mem _ rfl
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i hi i hi)
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hHB : (B + A).IsHermitian := (esw_herm_of_symm hB).add hA
  have hHs : (Wupd B i j s + A).IsHermitian :=
    esw_Wupd_herm hA (esw_herm_of_symm hB) i j s
  set G := GW A B z
  set G' := GW A (Wupd B i j s) z
  have hid : G' - G = ((B i j - s : ℝ) : ℂ) • (G' * deltaW i j * G) := by
    rw [esw_res_sub hHB hHs hz]
    conv_lhs => rw [show cplx (B + A) = cplx (Wupd B i j (B i j) + A) by rw [esw_Wupd_self hB]]
    rw [esw_cplx_Wupd_sub, Matrix.mul_smul, Matrix.smul_mul]
  have hent : ∀ a b, ‖G' a b - G a b‖ ≤ d * (‖G' a i‖ * ‖G j b‖ + ‖G' a j‖ * ‖G i b‖) := by
    intro a b
    have := congrFun (congrFun hid a) b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hd (esw_mul_delta_mul_le _ _ i j a b) (norm_nonneg _) hd0
  set X := max (max ‖G' i i‖ ‖G' i j‖) (max ‖G' j i‖ ‖G' j j‖) with hX
  have hXa : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)), ‖G' a b‖ ≤ X := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · rw [Set.mem_singleton_iff.1 hb]; exact (le_max_right _ _).trans (le_max_left _ _)
    · rw [Set.mem_singleton_iff.1 ha]; exact (le_max_left _ _).trans (le_max_right _ _)
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
      exact (le_max_right _ _).trans (le_max_right _ _)
  have hdiff : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖G' a b - G a b‖ ≤ 2 * d * M * X := by
    intro a ha b hb
    refine (hent a b).trans ?_
    have h1 := mul_le_mul (hXa a ha i hi) (hM j hj b hb) (norm_nonneg _) ((norm_nonneg _).trans
      (hXa a ha i hi))
    have h2 := mul_le_mul (hXa a ha j hj) (hM i hi b hb) (norm_nonneg _) ((norm_nonneg _).trans
      (hXa a ha i hi))
    nlinarith
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hXa i hi i hi)
  have hXle : X ≤ 2 * M := by
    have hb : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
        ‖G' a b‖ ≤ M + 2 * d * M * X := by
      intro a ha b hb
      have e : G' a b = G a b + (G' a b - G a b) := by ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hM a ha b hb) (hdiff a ha b hb))
    have hXM : X ≤ M + 2 * d * M * X := by
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> exact hb _ (by simp) _ (by simp)
    nlinarith
  intro a ha b hb
  refine ⟨(hdiff a ha b hb).trans ?_, (hXa a ha b hb).trans hXle⟩
  have := mul_le_mul_of_nonneg_left hXle (by positivity : 0 ≤ 2 * d * M)
  nlinarith

/-- The deterministic bound `|∂ⁿ f| ≤ n! C_b (192/η)^n`, `n ≤ 5`, uniformly in `W`. -/
private lemma esw_crude {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η) (Ea Eb : Fin l → ℝ) (i j : Fin N)
    (Wm : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) {n : ℕ} (hn : n ≤ 5) :
    |iteratedDeriv n (eswf F A η Ea Eb i j Wm) s| ≤ n.factorial * Cb * (192 * (1 / η)) ^ n := by
  have hgvc : ∀ (k : Fin l) (n : ℕ), ContDiff ℝ n fun t =>
      smCount (Wupd (eswSym Wm) i j t + A) η (Ea k) (Eb k) := fun k n =>
    esw_contDiff_smCount hA (esw_sym_herm Wm) hη (Ea k) (Eb k) i j n
  refine esw_comp_le hF hFb (fun t k => smCount (Wupd (eswSym Wm) i j t + A) η (Ea k) (Eb k))
    hgvc hn s (by positivity) fun i' h1 h2 k => ?_
  obtain ⟨n', rfl⟩ : ∃ n', i' = n' + 1 := ⟨i' - 1, by omega⟩
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * Complex.I).im := fun E => by simpa using hη
  have hb : ∀ E : ℝ, ∀ a b, ‖GW A (Wupd (eswSym Wm) i j s) ((E : ℂ) + η * Complex.I) a b‖ ≤
      1 / η := fun E a b => by
    have := esw_GW_entry_le (esw_Wupd_herm hA (esw_sym_herm Wm) i j s) (hz E) a b
    simpa using this
  exact esw_deriv_le_crude hA (esw_sym_herm Wm) hη (Ea k) (Eb k) i j s (by positivity)
    (hb (Ea k)) (hb (Eb k)) (by omega)

/-- The bound `|∂ⁿ f| ≤ n! C_b Θ`, `1 ≤ n ≤ 5`, at `W^{s}_{(ij)}`, when the entries of `G^W` on
`{i, j}²` at both window points are within `δ₀ ≤ 1` of `Π^W`, `|Π^W_{ab}| ≤ τ⁻¹` there, the
entries of `Π^W` at the two points differ by at most `κ`, `|W_{ij} − s| ≤ d`, and the constants
satisfy `2d(τ⁻¹ + 1) ≤ 1/2` and `480 (4(τ⁻¹ + 1))⁴ (8d(τ⁻¹ + 1)² + 2δ₀ + κ) ≤ Θ ≤ 1`. -/
private lemma esw_good {l : ℕ} {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η) (Ea Eb : Fin l → ℝ) (i j : Fin N)
    {τ δ₀ κ d Θ : ℝ} (hτ : 0 < τ) (hδ0 : 0 ≤ δ₀) (hδ₀ : δ₀ ≤ 1) (hκ0 : 0 ≤ κ) (hd0 : 0 ≤ d)
    (hP : ∀ k, ∀ a b, ‖piW A ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ τ⁻¹ ∧
      ‖piW A ((Eb k : ℂ) + η * Complex.I) a b‖ ≤ τ⁻¹)
    (hκ : ∀ k, ∀ a b, ‖piW A ((Eb k : ℂ) + η * Complex.I) a b -
      piW A ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ κ)
    (hdM : 2 * d * (τ⁻¹ + 1) ≤ 1 / 2)
    (hΘ : 480 * (4 * (τ⁻¹ + 1)) ^ 4 * (8 * d * (τ⁻¹ + 1) ^ 2 + 2 * δ₀ + κ) ≤ Θ) (hΘ1 : Θ ≤ 1)
    (Wm : Matrix (Fin N) (Fin N) ℝ)
    (hG : ∀ k, ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (eswSym Wm) ((Ea k : ℂ) + η * Complex.I) a b -
          piW A ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ δ₀ ∧
        ‖GW A (eswSym Wm) ((Eb k : ℂ) + η * Complex.I) a b -
          piW A ((Eb k : ℂ) + η * Complex.I) a b‖ ≤ δ₀)
    (s : ℝ) (hs : |eswSym Wm i j - s| ≤ d) {n : ℕ} (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    |iteratedDeriv n (eswf F A η Ea Eb i j Wm) s| ≤ n.factorial * Cb * Θ := by
  have hgvc : ∀ (k : Fin l) (n : ℕ), ContDiff ℝ n fun t =>
      smCount (Wupd (eswSym Wm) i j t + A) η (Ea k) (Eb k) := fun k n =>
    esw_contDiff_smCount hA (esw_sym_herm Wm) hη (Ea k) (Eb k) i j n
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  have hΘ0 : 0 ≤ Θ := le_trans (by positivity) hΘ
  refine esw_comp_le_small hF hFb
    (fun t k => smCount (Wupd (eswSym Wm) i j t + A) η (Ea k) (Eb k))
    hgvc hn1 hn5 s hΘ0 hΘ1 fun i' h1 h2 k => ?_
  obtain ⟨n', rfl⟩ : ∃ n', i' = n' + 1 := ⟨i' - 1, by omega⟩
  have hz : ∀ E : ℝ, 0 < ((E : ℂ) + η * Complex.I).im := fun E => by simpa using hη
  have hBsym := esw_sym_symm Wm
  have hMa : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (eswSym Wm) ((Ea k : ℂ) + η * Complex.I) a b‖ ≤ τ⁻¹ + 1 := by
    intro a ha b hb
    have e : GW A (eswSym Wm) ((Ea k : ℂ) + η * Complex.I) a b =
        piW A ((Ea k : ℂ) + η * Complex.I) a b +
          (GW A (eswSym Wm) ((Ea k : ℂ) + η * Complex.I) a b -
            piW A ((Ea k : ℂ) + η * Complex.I) a b) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hP k a b).1 ((hG k a ha b hb).1.trans hδ₀))
  have hMb : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (eswSym Wm) ((Eb k : ℂ) + η * Complex.I) a b‖ ≤ τ⁻¹ + 1 := by
    intro a ha b hb
    have e : GW A (eswSym Wm) ((Eb k : ℂ) + η * Complex.I) a b =
        piW A ((Eb k : ℂ) + η * Complex.I) a b +
          (GW A (eswSym Wm) ((Eb k : ℂ) + η * Complex.I) a b -
            piW A ((Eb k : ℂ) + η * Complex.I) a b) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hP k a b).2 ((hG k a ha b hb).2.trans hδ₀))
  have sa := esw_stab hA hBsym (hz (Ea k)) i j s hMa hs hdM
  have sb := esw_stab hA hBsym (hz (Eb k)) i j s hMb hs hdM
  have hdiff : ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (Wupd (eswSym Wm) i j s) ((Eb k : ℂ) + η * Complex.I) a b -
        GW A (Wupd (eswSym Wm) i j s) ((Ea k : ℂ) + η * Complex.I) a b‖ ≤
        8 * d * (τ⁻¹ + 1) ^ 2 + 2 * δ₀ + κ := by
    intro a ha b hb
    set Gb' := GW A (Wupd (eswSym Wm) i j s) ((Eb k : ℂ) + η * Complex.I) a b
    set Ga' := GW A (Wupd (eswSym Wm) i j s) ((Ea k : ℂ) + η * Complex.I) a b
    set Gb := GW A (eswSym Wm) ((Eb k : ℂ) + η * Complex.I) a b
    set Ga := GW A (eswSym Wm) ((Ea k : ℂ) + η * Complex.I) a b
    set Pb := piW A ((Eb k : ℂ) + η * Complex.I) a b
    set Pa := piW A ((Ea k : ℂ) + η * Complex.I) a b
    have e : Gb' - Ga' = (Gb' - Gb) + (Gb - Pb) + (Pb - Pa) - (Ga - Pa) - (Ga' - Ga) := by ring
    rw [e]
    have t1 := (sb a ha b hb).1
    have t2 := (hG k a ha b hb).2
    have t3 := hκ k a b
    have t4 := (hG k a ha b hb).1
    have t5 := (sa a ha b hb).1
    calc ‖(Gb' - Gb) + (Gb - Pb) + (Pb - Pa) - (Ga - Pa) - (Ga' - Ga)‖
        ≤ ‖Gb' - Gb‖ + ‖Gb - Pb‖ + ‖Pb - Pa‖ + ‖Ga - Pa‖ + ‖Ga' - Ga‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ 4 * d * (τ⁻¹ + 1) ^ 2 + δ₀ + κ + δ₀ + 4 * d * (τ⁻¹ + 1) ^ 2 := by
          gcongr
      _ = 8 * d * (τ⁻¹ + 1) ^ 2 + 2 * δ₀ + κ := by ring
  refine (esw_deriv_le_small hA (esw_sym_herm Wm) hη (Ea k) (Eb k) i j s
    (Wb := 2 * (τ⁻¹ + 1)) (by linarith) (fun a ha b hb => (sa a ha b hb).2)
    (fun a ha b hb => (sb a ha b hb).2) hdiff (by omega)).trans ?_
  have e : 2 * (2 * (τ⁻¹ + 1)) = 4 * (τ⁻¹ + 1) := by ring
  rw [e]
  exact hΘ

end WignerEntry

/-! ## Independence of an entry, and the comparison window -/

section Window

variable {N : ℕ}

/-- The entry `W_{ij}`, `i ≤ j`, is independent of the matrix `W^{0}_{(ij)}` of the other
entries. -/
private lemma esw_indep_entry {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) {i j : Fin N} (hij : i ≤ j) :
    IndepFun (fun ω => Wupd (W ω) i j 0) (fun ω => W ω i j) := by
  set q : UpperIdx N := ⟨(i, j), hij⟩ with hq
  set S : Finset (UpperIdx N) := Finset.univ.erase q with hS
  set T : Finset (UpperIdx N) := {q} with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_singleton_right]
    exact Finset.notMem_erase _ _
  have h := hW.indep.indepFun_finset S T hST fun p => hW.measurable p.1.1 p.1.2
  set φ : (S → ℝ) → Matrix (Fin N) (Fin N) ℝ := fun v a b =>
    if hm : (⟨(min a b, max a b), min_le_max⟩ : UpperIdx N) ∈ S then v ⟨_, hm⟩ else 0 with hφ
  set ψ : (T → ℝ) → ℝ := fun v => v ⟨q, Finset.mem_singleton_self _⟩ with hψ
  have hφm : Measurable φ := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    by_cases hm : (⟨(min a b, max a b), min_le_max⟩ : UpperIdx N) ∈ S
    · simpa [hφ, hm] using measurable_pi_apply (⟨_, hm⟩ : S)
    · simp [hφ, hm]
  have hψm : Measurable ψ := measurable_pi_apply _
  have h2 := h.comp hφm hψm
  have e1 : (φ ∘ fun ω (k : S) => W ω (k : UpperIdx N).1.1 (k : UpperIdx N).1.2) =
      fun ω => Wupd (W ω) i j 0 := by
    funext ω a b
    change φ (fun k : S => W ω (k : UpperIdx N).1.1 (k : UpperIdx N).1.2) a b = _
    by_cases hab : (a = i ∧ b = j) ∨ (a = j ∧ b = i)
    · have heq : (⟨(min a b, max a b), min_le_max⟩ : UpperIdx N) = q := by
        rw [hq]
        apply Subtype.ext
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [min_eq_left hij, max_eq_right hij]
        · simp [min_eq_right hij, max_eq_left hij]
      have hm : (⟨(min a b, max a b), min_le_max⟩ : UpperIdx N) ∉ S := by
        rw [heq, hS]
        exact Finset.notMem_erase _ _
      simp [hφ, hm, Wupd, hab]
    · have hm : (⟨(min a b, max a b), min_le_max⟩ : UpperIdx N) ∈ S := by
        rw [hS, Finset.mem_erase]
        refine ⟨fun he => hab ?_, Finset.mem_univ _⟩
        have he' := congrArg Subtype.val he
        simp only [hq, Prod.mk.injEq] at he'
        rcases le_total a b with h' | h'
        · rw [min_eq_left h', max_eq_right h'] at he'
          exact Or.inl he'
        · rw [min_eq_right h', max_eq_left h'] at he'
          exact Or.inr ⟨he'.2, he'.1⟩
      simp only [hφ, hm, Wupd, hab, dite_true, ite_false]
      rcases le_total a b with h' | h'
      · simp [min_eq_left h', max_eq_right h']
      · simp only [min_eq_right h', max_eq_left h']
        have := congrFun (congrFun (hW.symm ω) a) b
        simpa [Matrix.transpose_apply] using this
  have e2 : (ψ ∘ fun ω (k : T) => W ω (k : UpperIdx N).1.1 (k : UpperIdx N).1.2) =
      fun ω => W ω i j := by
    funext ω
    rfl
  rw [e1, e2] at h2
  exact h2

/-- The comparison window: for `N ≥ N₀`, `‖A‖ ≤ τ⁻¹ − 3` and the standing bound, each point
`E + iη`, `η = N^{-2/3-9ε}`, `|E − L₊| ≤ 3N^{-2/3+ε}`, lies in `edgeWinW` and has
`Ψ^W ≤ c_Ψ N^{-1/3+9ε}`; and `‖Π^W(E' + iη) − Π^W(E + iη)‖ ≤ K N^{-1/3+21ε/2}`. -/
private lemma esw_window {τ : ℝ} (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4) {ε : ℝ} (hε : 0 < ε)
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
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 ((esw_ev_small hy 6).and (esw_ev_small hy (8 / cs)))
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
    rw [hηdef, etaE, hw]; exact esw_rpow_le hN1 (by linarith)
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
    exact esw_rpow_le hN1 (by linarith)
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
      esw_rpow_le hN1 (by linarith)
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


/-! ## The good event and the derivative bounds on it -/

/-- For `N ≥ N₀` and the hypotheses of the swaps, there are a good set of matrices, on which the
entries of `G^W` on `{i, j}²` at the window points are within `c N^{-1/3+10ε}` of `Π^W`, and a
nonnegative `T` with `E T ≤ 8 l N^{-10}` and `T ≥ 1` off the good event; on the good set, near
`W_{ij} = 0`, the entry derivatives of orders `1, …, 5` are at most `n! C_b c_Θ N^{-1/3+11ε}`. -/
private lemma esw_setup (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ cΘ : ℝ, 0 ≤ cΘ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ)
      (i j : Fin N) (F : (Fin l → ℝ) → ℝ) (Cb : ℝ) (Ea Eb : Fin l → ℝ), i ≤ j →
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      ContDiff ℝ 5 F → (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
      (∀ k, |Ea k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) ∧
        |Eb k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) →
      cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε) ≤ 1 ∧
      ∃ (Good : Matrix (Fin N) (Fin N) ℝ → Prop) (TX : Ω → ℝ), (∀ ω, 0 ≤ TX ω) ∧
        Integrable TX ∧ ∫ ω, TX ω ≤ 8 * l * (N : ℝ) ^ (-(10 : ℝ)) ∧
        (∀ ω, Good (W ω) ∨ 1 ≤ TX ω) ∧
        ∀ (Wm : Matrix (Fin N) (Fin N) ℝ) (s : ℝ), Good Wm →
          |Wm i j| ≤ (N : ℝ) ^ (-1 / 2 + ε) → |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
          ∀ n : ℕ, 1 ≤ n → n ≤ 5 →
            |iteratedDeriv n (eswf F A (etaE N ε) Ea Eb i j Wm) s| ≤
              n.factorial * Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) := by
  obtain ⟨ε₁, D₁, hε₁, N₁, hlaw⟩ := anisoLawW_edgeWinW τ C ε ε 10 hτ hε hε1 hε
  obtain ⟨cψ, Kp, hcψ, hKp, N₂, hN₂1, hwin⟩ := esw_window hτ hτ4 hε hε1
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  set M : ℝ := τ⁻¹ + 1 with hM
  set cΘ : ℝ := 480 * (4 * M) ^ 4 * (16 * M ^ 2 + 2 * cψ + Kp) with hcΘ
  have hcΘ0 : 0 ≤ cΘ := by positivity
  have y1 : -1 / 3 + 10 * ε < 0 := by linarith
  have y2 : -1 / 2 + ε < 0 := by linarith
  have y3 : -1 / 3 + 11 * ε < 0 := by linarith
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 ((esw_ev_small y1 (2 * cψ)).and
    ((esw_ev_small y2 (4 * M)).and (esw_ev_small y3 (2 * cΘ))))
  refine ⟨ε₁, D₁, hε₁, cΘ, hcΘ0, max (max N₁ N₂) N₃,
    le_max_of_le_left (le_max_of_le_right hN₂1), ?_⟩
  intro N hN Ω _ _ A W i j F Cb Ea Eb hij hA hnA hW hSB hlawG hF hFb hE
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3' : N₃ ≤ N := le_trans (le_max_right _ _) hN
  have hNN : 1 ≤ N := hN₂1.trans hN2'
  obtain ⟨hc1, hc2, hc3⟩ := hN₃ N hN3'
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN
  have hn : (0 : ℝ) < N := by linarith
  have hη : 0 < etaE N ε := by unfold etaE; positivity
  have hlawW := hlaw N hN1' A W hA hnA hW hSB hlawG
  obtain ⟨hwinA, hpiA⟩ := hwin N hN2' A hA hnA hSB
  refine ⟨by linarith, ?_⟩
  set r : ℝ := (N : ℝ) ^ (-1 / 2 + ε) with hr
  set δ₀ : ℝ := cψ * (N : ℝ) ^ (-1 / 3 + 10 * ε) with hδ₀
  set κ : ℝ := Kp * (N : ℝ) ^ (-1 / 3 + 21 * ε / 2) with hκdef
  have hδ : ∀ E : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) →
      (N : ℝ) ^ ε * (PsiW (specOf A) ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) * 1 * 1) ≤ δ₀ := by
    intro E hE'
    have h := (hwinA E hE').2
    have e : (N : ℝ) ^ ε * (N : ℝ) ^ (-1 / 3 + 9 * ε) = (N : ℝ) ^ (-1 / 3 + 10 * ε) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    calc (N : ℝ) ^ ε * (PsiW (specOf A) ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) * 1 * 1)
        ≤ (N : ℝ) ^ ε * (cψ * (N : ℝ) ^ (-1 / 3 + 9 * ε)) := by
          rw [mul_one, mul_one]; gcongr
      _ = δ₀ := by rw [hδ₀, ← e]; ring
  have hPi : ∀ E : ℝ, |E - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) → ∀ a b : Fin N,
      ‖piW A ((E : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ τ⁻¹ := by
    intro E hE' a b
    have h := norm_piW_le hτ hA hSB (hwinA E hE').1.1 (Pi.single a 1) (Pi.single b 1)
    rwa [esw_testBilin_single, esw_testNorm_single, esw_testNorm_single, mul_one,
      mul_one] at h
  have hκ : ∀ k, ∀ a b : Fin N, ‖piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b -
      piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ κ := by
    intro k a b
    have h := (esw_entry_le_norm (piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) -
      piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I)) a b).trans
      (hpiA (Ea k) (Eb k) (hE k).1 (hE k).2)
    rwa [Matrix.sub_apply] at h
  -- the events
  set ιJ : Fin 2 → Fin N := ![i, j] with hιJ
  have hJ : ∀ a ∈ ({i, j} : Set (Fin N)), ∃ q : Fin 2, ιJ q = a := by
    intro a ha
    rcases ha with rfl | ha
    · exact ⟨0, rfl⟩
    · exact ⟨1, (Set.mem_singleton_iff.1 ha).symm⟩
  set zz : Fin l → Bool → ℂ := fun k b =>
    if b then (Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I else (Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I
    with hzz
  set P : Fin l × Bool × Fin 2 × Fin 2 → Set Ω := fun x => {ω |
    ‖GW A (W ω) (zz x.1 x.2.1) (ιJ x.2.2.1) (ιJ x.2.2.2) -
      piW A (zz x.1 x.2.1) (ιJ x.2.2.1) (ιJ x.2.2.2)‖ ≤ δ₀} with hP
  have hPc : ∀ x, (ℙ : Measure Ω) (P x)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(10 : ℝ))) := by
    rintro ⟨k, b, q, c⟩
    have hzw : zz k b ∈ edgeWinW τ N (specOf A) ε ∧
        (N : ℝ) ^ ε * (PsiW (specOf A) (zz k b) * 1 * 1) ≤ δ₀ := by
      cases b
      · exact ⟨(hwinA _ (hE k).2).1, hδ _ (hE k).2⟩
      · exact ⟨(hwinA _ (hE k).1).1, hδ _ (hE k).1⟩
    have hd := hlawW (zz k b) hzw.1 (Pi.single (ιJ q) 1) (Pi.single (ιJ c) 1)
    refine le_trans (measure_mono ?_) hd
    intro ω hω
    simp only [Set.mem_compl_iff, hP, Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_ofPred_eq, esw_testBilin_single, esw_testNorm_single, Matrix.sub_apply]
    linarith [hzw.2]
  obtain ⟨TX, hTX0, hTXi, hTXint, hTX1⟩ := esw_events P (by positivity) hPc
  have hcard : (Fintype.card (Fin l × Bool × Fin 2 × Fin 2) : ℝ) = 8 * l := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  rw [hcard] at hTXint
  refine ⟨fun Wm => ∀ k, ∀ a ∈ ({i, j} : Set (Fin N)), ∀ b ∈ ({i, j} : Set (Fin N)),
      ‖GW A (eswSym Wm) ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b -
          piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ δ₀ ∧
        ‖GW A (eswSym Wm) ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b -
          piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ δ₀,
    TX, hTX0, hTXi, hTXint, fun ω => ?_, ?_⟩
  · rcases hTX1 ω with h | h
    · left
      intro k a ha b hb
      obtain ⟨q, rfl⟩ := hJ a ha
      obtain ⟨c, rfl⟩ := hJ b hb
      rw [esw_sym_eq (hW.symm ω)]
      exact ⟨h ⟨k, true, q, c⟩, h ⟨k, false, q, c⟩⟩
    · exact Or.inr h
  · intro Wm s hG hWm hs n hn1 hn5
    have hr0 : 0 ≤ r := by positivity
    have hδ0 : 0 ≤ δ₀ := by positivity
    have hκ0 : 0 ≤ κ := by positivity
    have hs' : |eswSym Wm i j - s| ≤ 2 * r := by
      rw [esw_sym_apply Wm hij]
      have := abs_sub (Wm i j) s
      linarith
    have hrle : r ≤ (N : ℝ) ^ (-1 / 3 + 11 * ε) := esw_rpow_le hNN (by linarith)
    have h10 : (N : ℝ) ^ (-1 / 3 + 10 * ε) ≤ (N : ℝ) ^ (-1 / 3 + 11 * ε) :=
      esw_rpow_le hNN (by linarith)
    have h21 : (N : ℝ) ^ (-1 / 3 + 21 * ε / 2) ≤ (N : ℝ) ^ (-1 / 3 + 11 * ε) :=
      esw_rpow_le hNN (by linarith)
    have hΘ : 480 * (4 * (τ⁻¹ + 1)) ^ 4 * (8 * (2 * r) * (τ⁻¹ + 1) ^ 2 + 2 * δ₀ + κ) ≤
        cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε) := by
      have hsum : 8 * (2 * r) * (τ⁻¹ + 1) ^ 2 + 2 * δ₀ + κ ≤
          (16 * M ^ 2 + 2 * cψ + Kp) * (N : ℝ) ^ (-1 / 3 + 11 * ε) := by
        rw [hδ₀, hκdef, hM]
        have a1 := mul_le_mul_of_nonneg_left hrle (by positivity : (0 : ℝ) ≤ 16 * (τ⁻¹ + 1) ^ 2)
        have a2 := mul_le_mul_of_nonneg_left h10 (by positivity : (0 : ℝ) ≤ 2 * cψ)
        have a3 := mul_le_mul_of_nonneg_left h21 hKp
        nlinarith
      calc 480 * (4 * (τ⁻¹ + 1)) ^ 4 * (8 * (2 * r) * (τ⁻¹ + 1) ^ 2 + 2 * δ₀ + κ)
          ≤ 480 * (4 * (τ⁻¹ + 1)) ^ 4 * ((16 * M ^ 2 + 2 * cψ + Kp) *
            (N : ℝ) ^ (-1 / 3 + 11 * ε)) := by gcongr
        _ = cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε) := by rw [hcΘ, hM]; ring
    have hδ1 : δ₀ ≤ 1 := by rw [hδ₀]; linarith
    have hd0 : 0 ≤ 2 * r := by linarith
    have hdM : 2 * (2 * r) * (τ⁻¹ + 1) ≤ 1 / 2 := by
      have : 2 * (2 * r) * (τ⁻¹ + 1) = 4 * M * r := by rw [hM]; ring
      rw [this]; exact hc2
    have hΘ1 : cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε) ≤ 1 := by linarith
    have hP2 : ∀ k, ∀ a b : Fin N,
        ‖piW A ((Ea k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ τ⁻¹ ∧
          ‖piW A ((Eb k : ℂ) + (etaE N ε : ℝ) * Complex.I) a b‖ ≤ τ⁻¹ :=
      fun k a b => ⟨hPi _ (hE k).1 a b, hPi _ (hE k).2 a b⟩
    exact esw_good (τ := τ) (δ₀ := δ₀) (κ := κ) (d := 2 * r)
      (Θ := cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) hF hFb hA hη Ea Eb i j hτ hδ0 hδ1 hκ0 hd0
      hP2 hκ hdM hΘ hΘ1 Wm hG s hs' hn1 hn5

end Window

/-! ## The exponent bookkeeping -/

section Arith

/-- The off-diagonal bookkeeping: the remainder, tail and coefficient-move bounds sum to at most
`K C_b N^{-7/3+12ε}`. -/
private lemma esw_final_off {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    {p : ℕ} (hp : 8 ≤ (p : ℝ) * ε) {Cb cΘ c2 c3 c4 c2p c4p cp L : ℝ} (hCb : 0 ≤ Cb)
    (hcΘ : 0 ≤ cΘ) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hc2p : 0 ≤ c2p)
    (hc4p : 0 ≤ c4p) (hcp : 0 ≤ cp) (hL : 0 ≤ L) :
    2 * (Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) * ((N : ℝ) ^ (-(4 : ℝ) / 2) * c4) +
        Cb * (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 4 *
          ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * c4p +
            (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (8 * L * (N : ℝ) ^ (-(10 : ℝ)) +
              (N : ℝ) ^ (-((p : ℝ) * ε)) * cp))) +
      2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3) / 6 *
        (60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * c2) +
          60 * Cb * (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 5 *
            ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * c2p +
              (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (8 * L * (N : ℝ) ^ (-(10 : ℝ))))) ≤
      (2 * (cΘ * c4 + 192 ^ 4 * (c4p + 8 * L + cp)) +
        c3 / 3 * (60 * c2 + 60 * 192 ^ 5 * (c2p + 8 * L))) * Cb *
          (N : ℝ) ^ (-7 / 3 + 12 * ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := (N : ℝ) ^ (-7 / 3 + 12 * ε) with hP
  have hP0 : 0 ≤ P := by positivity
  have hW4 : (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 4 = 192 ^ 4 * (N : ℝ) ^ (8 / 3 + 36 * ε) := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (2 / 3 + 9 * ε)), ← Real.rpow_mul hn.le]
    ring_nf
  have hW5 : (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 5 = 192 ^ 5 * (N : ℝ) ^ (10 / 3 + 45 * ε) := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (2 / 3 + 9 * ε)), ← Real.rpow_mul hn.le]
    ring_nf
  have r2 : ∀ x y : ℝ, (N : ℝ) ^ x * (N : ℝ) ^ y = (N : ℝ) ^ (x + y) := fun x y =>
    (Real.rpow_add hn x y).symm
  have e1 : (N : ℝ) ^ (-1 / 3 + 11 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 2) ≤ P := by
    rw [r2]; exact esw_rpow_le hN (by linarith)
  have e2 : (N : ℝ) ^ (8 / 3 + 36 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) ≤ P := by
    rw [r2]; exact esw_rpow_le hN (by linarith)
  have e3 : (N : ℝ) ^ (8 / 3 + 36 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
      (N : ℝ) ^ (-(10 : ℝ))) ≤ P := by
    rw [r2, r2]; exact esw_rpow_le hN (by linarith)
  have e4 : (N : ℝ) ^ (8 / 3 + 36 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
      (N : ℝ) ^ (-((p : ℝ) * ε))) ≤ P := by
    rw [r2, r2]; exact esw_rpow_le hN (by linarith)
  have e5 : (N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(2 : ℝ) / 2) ≤ P := by
    rw [r2]; exact esw_rpow_le hN (by linarith)
  have e6 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ (10 / 3 + 45 * ε) *
      (N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε)) ≤ P := by
    rw [r2, r2]; exact esw_rpow_le hN (by linarith)
  have e7 : (N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ (10 / 3 + 45 * ε) *
      ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (N : ℝ) ^ (-(10 : ℝ)))) ≤ P := by
    rw [r2, r2, r2]; exact esw_rpow_le hN (by linarith)
  rw [hW4, hW5]
  have expand : 2 * (Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) * ((N : ℝ) ^ (-(4 : ℝ) / 2) * c4) +
        Cb * (192 ^ 4 * (N : ℝ) ^ (8 / 3 + 36 * ε)) *
          ((N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε) * c4p +
            (N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) * (8 * L * (N : ℝ) ^ (-(10 : ℝ)) +
              (N : ℝ) ^ (-((p : ℝ) * ε)) * cp))) +
      2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3) / 6 *
        (60 * Cb * ((N : ℝ) ^ (-(2 : ℝ) / 2) * c2) +
          60 * Cb * (192 ^ 5 * (N : ℝ) ^ (10 / 3 + 45 * ε)) *
            ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * c2p +
              (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (8 * L * (N : ℝ) ^ (-(10 : ℝ))))) =
      Cb * (2 * (cΘ * c4) * ((N : ℝ) ^ (-1 / 3 + 11 * ε) * (N : ℝ) ^ (-(4 : ℝ) / 2)) +
        2 * 192 ^ 4 * (c4p * ((N : ℝ) ^ (8 / 3 + 36 * ε) *
          (N : ℝ) ^ (-(4 : ℝ) / 2 - p * ε)) +
          8 * L * ((N : ℝ) ^ (8 / 3 + 36 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
            (N : ℝ) ^ (-(10 : ℝ)))) +
          cp * ((N : ℝ) ^ (8 / 3 + 36 * ε) * ((N : ℝ) ^ (-(4 : ℝ) / 2 + 4 * ε) *
            (N : ℝ) ^ (-((p : ℝ) * ε))))) +
        c3 / 3 * (60 * c2 * ((N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (-(2 : ℝ) / 2)) +
          60 * 192 ^ 5 * (c2p * ((N : ℝ) ^ (-(3 : ℝ) / 2) *
            ((N : ℝ) ^ (10 / 3 + 45 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε))) +
            8 * L * ((N : ℝ) ^ (-(3 : ℝ) / 2) * ((N : ℝ) ^ (10 / 3 + 45 * ε) *
              ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (N : ℝ) ^ (-(10 : ℝ)))))))) := by
    ring
  rw [expand]
  calc _ ≤ Cb * (2 * (cΘ * c4) * P + 2 * 192 ^ 4 * (c4p * P + 8 * L * P + cp * P) +
        c3 / 3 * (60 * c2 * P + 60 * 192 ^ 5 * (c2p * P + 8 * L * P))) := by
        gcongr
    _ = _ := by ring

/-- The diagonal bookkeeping: twice the order-two remainder and tail bounds is at most
`K C_b N^{-4/3+12ε}`. -/
private lemma esw_final_diag {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    {p : ℕ} (hp : 8 ≤ (p : ℝ) * ε) {Cb cΘ c2 c2p cp L : ℝ} (hCb : 0 ≤ Cb)
    (hcΘ : 0 ≤ cΘ) (hc2 : 0 ≤ c2) (hc2p : 0 ≤ c2p) (hcp : 0 ≤ cp) (hL : 0 ≤ L) :
    2 * (Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) * ((N : ℝ) ^ (-(2 : ℝ) / 2) * c2) +
        Cb * (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 2 *
          ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * c2p +
            (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (8 * L * (N : ℝ) ^ (-(10 : ℝ)) +
              (N : ℝ) ^ (-((p : ℝ) * ε)) * cp))) ≤
      2 * (cΘ * c2 + 192 ^ 2 * (c2p + 8 * L + cp)) * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := (N : ℝ) ^ (-4 / 3 + 12 * ε) with hP
  have hW2 : (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ 2 = 192 ^ 2 * (N : ℝ) ^ (4 / 3 + 18 * ε) := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (2 / 3 + 9 * ε)), ← Real.rpow_mul hn.le]
    ring_nf
  have r2 : ∀ x y : ℝ, (N : ℝ) ^ x * (N : ℝ) ^ y = (N : ℝ) ^ (x + y) := fun x y =>
    (Real.rpow_add hn x y).symm
  have e1 : (N : ℝ) ^ (-1 / 3 + 11 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 2) ≤ P := by
    rw [r2]; exact esw_rpow_le hN (by linarith)
  have e2 : (N : ℝ) ^ (4 / 3 + 18 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) ≤ P := by
    rw [r2]; exact esw_rpow_le hN (by linarith)
  have e3 : (N : ℝ) ^ (4 / 3 + 18 * ε) * ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) *
      (N : ℝ) ^ (-(10 : ℝ))) ≤ P := by
    rw [r2, r2]; exact esw_rpow_le hN (by linarith)
  have e4 : (N : ℝ) ^ (4 / 3 + 18 * ε) * ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) *
      (N : ℝ) ^ (-((p : ℝ) * ε))) ≤ P := by
    rw [r2, r2]; exact esw_rpow_le hN (by linarith)
  rw [hW2]
  have expand : 2 * (Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) * ((N : ℝ) ^ (-(2 : ℝ) / 2) * c2) +
        Cb * (192 ^ 2 * (N : ℝ) ^ (4 / 3 + 18 * ε)) *
          ((N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε) * c2p +
            (N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) * (8 * L * (N : ℝ) ^ (-(10 : ℝ)) +
              (N : ℝ) ^ (-((p : ℝ) * ε)) * cp))) =
      2 * Cb * (cΘ * c2 * ((N : ℝ) ^ (-1 / 3 + 11 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 2)) +
        192 ^ 2 * (c2p * ((N : ℝ) ^ (4 / 3 + 18 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 2 - p * ε)) +
          8 * L * ((N : ℝ) ^ (4 / 3 + 18 * ε) * ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) *
            (N : ℝ) ^ (-(10 : ℝ)))) +
          cp * ((N : ℝ) ^ (4 / 3 + 18 * ε) * ((N : ℝ) ^ (-(2 : ℝ) / 2 + 2 * ε) *
            (N : ℝ) ^ (-((p : ℝ) * ε)))))) := by
    ring
  rw [expand]
  calc _ ≤ 2 * Cb * (cΘ * c2 * P + 192 ^ 2 * (c2p * P + 8 * L * P + cp * P)) := by
        gcongr
    _ = _ := by ring

end Arith

/-- The common facts for both swaps at `N ≥ 1`: `η > 0`, smoothness and measurability of the
entry function, and the deterministic bound with `D = 192 N^{2/3+9ε} ≥ 1`. -/
private lemma esw_common {N : ℕ} (hn1 : (1 : ℝ) ≤ N) {ε : ℝ} (hε : 0 < ε) {l : ℕ}
    {F : (Fin l → ℝ) → ℝ} {Cb : ℝ} (hF : ContDiff ℝ 5 F)
    (hFb : ∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (Ea Eb : Fin l → ℝ) (i j : Fin N) :
    0 < etaE N ε ∧
      (∀ n ≤ 5, ∀ (Wm : Matrix (Fin N) (Fin N) ℝ) (s : ℝ),
        |iteratedDeriv n (eswf F A (etaE N ε) Ea Eb i j Wm) s| ≤
          n.factorial * Cb * (192 * (N : ℝ) ^ (2 / 3 + 9 * ε)) ^ n) ∧
      1 ≤ 192 * (N : ℝ) ^ (2 / 3 + 9 * ε) ∧
      (∀ n ≤ 5, Measurable fun q : Matrix (Fin N) (Fin N) ℝ × ℝ =>
        iteratedDeriv n (eswf F A (etaE N ε) Ea Eb i j q.1) q.2) ∧
      ∀ Wm, ContDiff ℝ 5 (eswf F A (etaE N ε) Ea Eb i j Wm) := by
  have hn : (0 : ℝ) < N := by linarith
  have hη : 0 < etaE N ε := by unfold etaE; positivity
  have hηinv : 1 / etaE N ε = (N : ℝ) ^ (2 / 3 + 9 * ε) := by
    rw [etaE, one_div, ← Real.rpow_neg hn.le]
    congr 1; ring
  have hfc := esw_f_contDiff hF hA hη Ea Eb i j
  refine ⟨hη, fun n hn5 Wm s => ?_, ?_, esw_measurable_iteratedDeriv _
    (esw_f_continuous hF hA hη Ea Eb i j).measurable 5 hfc, hfc⟩
  · have h := esw_crude hF hFb hA hη Ea Eb i j Wm s hn5
    rwa [hηinv] at h
  · have := Real.one_le_rpow hn1 (by linarith : (0 : ℝ) ≤ 2 / 3 + 9 * ε)
    linarith

/-! ## The swaps

The one-entry steps of the Green function comparison near the edge in the proof of
Theorem 12.5, on the comparison window `|E − L₊| ≤ 3N^{-2/3+ε}`, `η = N^{-2/3-9ε}`, where
`Ψ^W ≤ N^{-1/3+c}` (the remark in that proof on hypothesis (b) of Theorem 12.2). -/

/-- One off-diagonal swap: for `y₁`, `y₀` independent of `W` with mean `0` and variance `1/N`,
`E F(W^{y₁}_{(ij)}) - E F(W^{y₀}_{(ij)})` is the third-moment term at `W` up to
`K C_b N^{-7/3+12ε}`. -/
theorem smFW_swap_off (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) (y₁ y₀ : Ω → ℝ)
      (i j : Fin N) (F : (Fin l → ℝ) → ℝ) (Cb : ℝ) (Ea Eb : Fin l → ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) → i < j →
      IndepFun W y₁ → IndepFun W y₀ → Measurable y₁ → Measurable y₀ →
      (∫ ω, y₁ ω) = 0 → (∫ ω, y₀ ω) = 0 → (∫ ω, y₁ ω ^ 2) = 1 / (N : ℝ) →
      (∫ ω, y₀ ω ^ 2) = 1 / (N : ℝ) →
      (∀ p : ℕ, Integrable (fun ω => |Real.sqrt N * y₁ ω| ^ p) ∧
        ∫ ω, |Real.sqrt N * y₁ ω| ^ p ≤ C p) →
      (∀ p : ℕ, Integrable (fun ω => |Real.sqrt N * y₀ ω| ^ p) ∧
        ∫ ω, |Real.sqrt N * y₀ ω| ^ p ≤ C p) →
      ContDiff ℝ 5 F → (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
      (∀ k, |Ea k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) ∧
        |Eb k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) →
      |((∫ ω, smFW F A (Wupd (W ω) i j (y₁ ω)) (etaE N ε) Ea Eb) -
            (∫ ω, smFW F A (Wupd (W ω) i j (y₀ ω)) (etaE N ε) Ea Eb)) -
          ((∫ ω, y₁ ω ^ 3) - (∫ ω, y₀ ω ^ 3)) / 6 *
            (∫ ω, smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j))| ≤
        K * Cb * (N : ℝ) ^ (-7 / 3 + 12 * ε) := by
  obtain ⟨ε₁, D₁, hε₁, cΘ, hcΘ0, N₀, hN₀1, hset⟩ := esw_setup τ C l ε hτ hτ4 hε hε1
  obtain ⟨p, hp⟩ : ∃ p : ℕ, 8 ≤ (p : ℝ) * ε := ⟨⌈8 / ε⌉₊, by
    calc (8 : ℝ) = 8 / ε * ε := by field_simp
      _ ≤ (⌈8 / ε⌉₊ : ℝ) * ε := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε.le⟩
  refine ⟨ε₁, D₁, hε₁, 2 * (cΘ * C 4 + 192 ^ 4 * (C (4 + p) + 8 * l + C p)) +
    C 3 / 3 * (60 * C 2 + 60 * 192 ^ 5 * (C (2 + p) + 8 * l)), N₀, ?_⟩
  intro N hN Ω _ _ A W y₁ y₀ i j F Cb Ea Eb hA hnA hW hSB hlawG hij hi₁ hi₀ hy₁ hy₀ hE₁ hE₀
    hV₁ hV₀ hM₁ hM₀ hF hFb hwin
  have hNN : 1 ≤ N := hN₀1.trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN
  have hn : (0 : ℝ) < N := by linarith
  obtain ⟨hΘ1, Good, TX, hTX0, hTXi, hTXint, hTXg, hgood⟩ :=
    hset N hN A W i j F Cb Ea Eb hij.le hA hnA hW hSB hlawG hF hFb hwin
  obtain ⟨hη, hcrude, hD1, hΦ, hfc⟩ := esw_common hn1 hε hF hFb hA Ea Eb i j
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hC : ∀ q, 0 ≤ C q := fun q => (integral_nonneg fun ω => by positivity).trans (hM₁ q).2
  have hWm : Measurable W := Measurable.of_eval_matrix W fun s u => hW.measurable s u
  have hfX := esw_f_Wupd F A (etaE N ε) Ea Eb i j
  have hfW : ∀ ω, eswf F A (etaE N ε) Ea Eb i j (W ω) =
      fun t => smFW F A (Wupd (W ω) i j t) (etaE N ε) Ea Eb := fun ω => by
    funext t
    simp only [eswf, esw_sym_eq (hW.symm ω)]
  have g1 : (∫ ω, smFW F A (Wupd (W ω) i j (y₁ ω)) (etaE N ε) Ea Eb) =
      ∫ ω, eswf F A (etaE N ε) Ea Eb i j (W ω) (y₁ ω) := by
    congr 1; funext ω; rw [hfW]
  have g0 : (∫ ω, smFW F A (Wupd (W ω) i j (y₀ ω)) (etaE N ε) Ea Eb) =
      ∫ ω, eswf F A (etaE N ε) Ea Eb i j (W ω) (y₀ ω) := by
    congr 1; funext ω; rw [hfW]
  have g3 : (∫ ω, smTW 3 F A (W ω) (etaE N ε) Ea Eb i j (W ω i j)) =
      ∫ ω, iteratedDeriv 3 (eswf F A (etaE N ε) Ea Eb i j (W ω)) (W ω i j) := by
    congr 1; funext ω; rw [hfW]; rfl
  rw [g1, g0, g3]
  clear hfW g1 g0 g3
  generalize eswf F A (etaE N ε) Ea Eb i j = f at hfX hgood hcrude hΦ hfc ⊢
  have hind : IndepFun (fun ω => iteratedDeriv 4 (f (W ω)) 0) (fun ω => W ω i j) := by
    have hm4 : Measurable fun Wm => iteratedDeriv 4 (f Wm) 0 := by
      have h := (hΦ 4 (by norm_num)).comp (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
      exact h
    have h := (esw_indep_entry hW hij.le).comp hm4 measurable_id
    have e : ((fun Wm => iteratedDeriv 4 (f Wm) 0) ∘ fun ω => Wupd (W ω) i j 0) =
        fun ω => iteratedDeriv 4 (f (W ω)) 0 := by
      funext ω
      simp only [Function.comp_apply, hfX]
    rw [e] at h
    exact h
  have hΘ0 : 0 ≤ cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε) := mul_nonneg hcΘ0 (by positivity)
  refine le_trans (esw_prob_off hNN (ε := ε) C p hWm (fun Wm => Wm i j) (hW.measurable i j)
    (hW.mean i j) (fun q => ⟨hW.integrable_moment q i j, hW.moment q i j⟩)
    f hfc hΦ hind hCb hD1 hΘ0 hΘ1
    Good hcrude hgood hTX0 hTXi hTXint hTXg hi₁ hi₀ hy₁ hy₀ hE₁ hE₀ hV₁ hV₀ hM₁ hM₀) ?_
  exact esw_final_off hNN hε hε1 hp hCb hcΘ0 (hC 2) (hC 3) (hC 4) (hC (2 + p)) (hC (4 + p))
    (hC p) (Nat.cast_nonneg l)

/-- One diagonal swap: for `y₁`, `y₀` independent of `W` with mean `0` and variances in
`[1/N, 2/N]` (the diagonal variance `1/N` of `W` against `2/N` of the GOE),
`|E F(W^{y₁}_{(ii)}) - E F(W^{y₀}_{(ii)})| ≤ K C_b N^{-4/3+12ε}`. -/
theorem smFW_swap_diag (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hτ4 : τ ≤ 1 / 4)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ ε₁ D₁ : ℝ, 0 < ε₁ ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (A : Matrix (Fin N) (Fin N) ℝ) (W : Ω → Matrix (Fin N) (Fin N) ℝ) (y₁ y₀ : Ω → ℝ)
      (i : Fin N) (F : (Fin l → ℝ) → ℝ) (Cb : ℝ) (Ea Eb : Fin l → ℝ),
      A.IsHermitian → ‖A‖ ≤ τ⁻¹ - 3 → WigClassEntries C N W →
      StandingBoundW τ (specOf A) (domW τ N) →
      EntrywiseLawWAt N ε₁ D₁ (diagonal (specOf A)) (goeW N) (domW τ N) →
      IndepFun W y₁ → IndepFun W y₀ → Measurable y₁ → Measurable y₀ →
      (∫ ω, y₁ ω) = 0 → (∫ ω, y₀ ω) = 0 →
      1 / (N : ℝ) ≤ (∫ ω, y₁ ω ^ 2) → (∫ ω, y₁ ω ^ 2) ≤ 2 / (N : ℝ) →
      1 / (N : ℝ) ≤ (∫ ω, y₀ ω ^ 2) → (∫ ω, y₀ ω ^ 2) ≤ 2 / (N : ℝ) →
      (∀ p : ℕ, Integrable (fun ω => |Real.sqrt N * y₁ ω| ^ p) ∧
        ∫ ω, |Real.sqrt N * y₁ ω| ^ p ≤ C p) →
      (∀ p : ℕ, Integrable (fun ω => |Real.sqrt N * y₀ ω| ^ p) ∧
        ∫ ω, |Real.sqrt N * y₀ ω| ^ p ≤ C p) →
      ContDiff ℝ 5 F → (∀ m ≤ 5, ∀ x, ‖iteratedFDeriv ℝ m F x‖ ≤ Cb) →
      (∀ k, |Ea k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) ∧
        |Eb k - LpW (specOf A)| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε)) →
      |(∫ ω, smFW F A (Wupd (W ω) i i (y₁ ω)) (etaE N ε) Ea Eb) -
          (∫ ω, smFW F A (Wupd (W ω) i i (y₀ ω)) (etaE N ε) Ea Eb)| ≤
        K * Cb * (N : ℝ) ^ (-4 / 3 + 12 * ε) := by
  obtain ⟨ε₁, D₁, hε₁, cΘ, hcΘ0, N₀, hN₀1, hset⟩ := esw_setup τ C l ε hτ hτ4 hε hε1
  obtain ⟨p, hp⟩ : ∃ p : ℕ, 8 ≤ (p : ℝ) * ε := ⟨⌈8 / ε⌉₊, by
    calc (8 : ℝ) = 8 / ε * ε := by field_simp
      _ ≤ (⌈8 / ε⌉₊ : ℝ) * ε := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε.le⟩
  refine ⟨ε₁, D₁, hε₁, 2 * (cΘ * C 2 + 192 ^ 2 * (C (2 + p) + 8 * l + C p)), N₀, ?_⟩
  intro N hN Ω _ _ A W y₁ y₀ i F Cb Ea Eb hA hnA hW hSB hlawG hi₁ hi₀ hy₁ hy₀ hE₁ hE₀
    hV₁ hV₁' hV₀ hV₀' hM₁ hM₀ hF hFb hwin
  have hNN : 1 ≤ N := hN₀1.trans hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hNN
  obtain ⟨hΘ1, Good, TX, hTX0, hTXi, hTXint, hTXg, hgood⟩ :=
    hset N hN A W i i F Cb Ea Eb le_rfl hA hnA hW hSB hlawG hF hFb hwin
  obtain ⟨hη, hcrude, hD1, hΦ, hfc⟩ := esw_common hn1 hε hF hFb hA Ea Eb i i
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hC : ∀ q, 0 ≤ C q := fun q => (integral_nonneg fun ω => by positivity).trans (hM₁ q).2
  have hWm : Measurable W := Measurable.of_eval_matrix W fun s u => hW.measurable s u
  have hfW : ∀ ω, eswf F A (etaE N ε) Ea Eb i i (W ω) =
      fun t => smFW F A (Wupd (W ω) i i t) (etaE N ε) Ea Eb := fun ω => by
    funext t
    simp only [eswf, esw_sym_eq (hW.symm ω)]
  have g1 : (∫ ω, smFW F A (Wupd (W ω) i i (y₁ ω)) (etaE N ε) Ea Eb) =
      ∫ ω, eswf F A (etaE N ε) Ea Eb i i (W ω) (y₁ ω) := by
    congr 1; funext ω; rw [hfW]
  have g0 : (∫ ω, smFW F A (Wupd (W ω) i i (y₀ ω)) (etaE N ε) Ea Eb) =
      ∫ ω, eswf F A (etaE N ε) Ea Eb i i (W ω) (y₀ ω) := by
    congr 1; funext ω; rw [hfW]
  rw [g1, g0]
  clear hfW g1 g0
  generalize eswf F A (etaE N ε) Ea Eb i i = f at hgood hcrude hΦ hfc ⊢
  have hΘ0 : 0 ≤ cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε) := mul_nonneg hcΘ0 (by positivity)
  have hgood2 : ∀ (Wm : Matrix (Fin N) (Fin N) ℝ) (s : ℝ), Good Wm →
      |(fun Wm : Matrix (Fin N) (Fin N) ℝ => Wm i i) Wm| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |s| ≤ (N : ℝ) ^ (-1 / 2 + ε) →
      |iteratedDeriv 2 (f Wm) s| ≤ 2 * Cb * (cΘ * (N : ℝ) ^ (-1 / 3 + 11 * ε)) := by
    intro Wm s hG h1 h2
    have h := hgood Wm s hG h1 h2 2 (by norm_num) (by norm_num)
    rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 by norm_num [Nat.factorial]] at h
    exact h
  refine le_trans (esw_prob_diag hNN (ε := ε) C p hWm (fun Wm => Wm i i)
    (fun q => ⟨hW.integrable_moment q i i, hW.moment q i i⟩)
    f (fun Wm => (hfc Wm).of_le (by norm_num))
    (fun n hn => hΦ n (by omega)) hCb (by linarith) hΘ0 Good
    (fun n hn Wm s => hcrude n (by omega) Wm s) hgood2
    hTX0 hTXi hTXint hTXg hi₁ hi₀ hy₁ hy₀ hE₁ hE₀ hM₁ hM₀) ?_
  exact esw_final_diag hNN hε hε1 hp hCb hcΘ0 (hC 2) (hC (2 + p)) (hC p) (Nat.cast_nonneg l)


/-- The entry derivative of `𝒳` at `N = 2`, `A = aEx 2`, `W = 0`, entry `(0, 1)`, `η = 1`. -/
example : HasDerivAt (fun t => smCount (Wupd 0 0 1 t + aEx 2) 1 0 1)
    (-(1 / Real.pi) *
      ((trace (deltaW (0 : Fin 2) 1 * GW (aEx 2) (Wupd 0 0 1 0) (1 + (1 : ℝ) * Complex.I))).im -
        (trace (deltaW (0 : Fin 2) 1 * GW (aEx 2) (Wupd 0 0 1 0) (0 + (1 : ℝ) * Complex.I))).im))
    0 := by
  have h := hasDerivAt_smCountW (aEx_isHermitian 2) (Matrix.isHermitian_zero) one_pos 0 1
    (0 : Fin 2) 1 0
  simpa using h


#print axioms smFW
#print axioms smTW
#print axioms hasDerivAt_smCountW
#print axioms smFW_swap_off
#print axioms smFW_swap_diag

end Anisotropic
