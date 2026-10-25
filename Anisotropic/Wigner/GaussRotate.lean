import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Gaussian.Invariance
import Anisotropic.Wigner.Defs
import Anisotropic.Wigner.GOE
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Transfer of the GOE laws from `D` to `A` by orthogonal invariance

For a real symmetric `A = U D Uᵀ` with `D = diag(specOf A)`, the resolvent satisfies
`G^W(A, W) = U G^W(D, Uᵀ W U) Uᵀ` and `Π^W(A) = U Π^W(D) Uᵀ`, the centring `m^W` and the control
`Ψ^W` coincide for `A` and `D`, and `Uᵀ W U` has the law of `W` for a GOE matrix `W`. Hence
the failure probabilities of the laws of Definition 12.1 for `A` and for `D` agree. -/

/-- The real orthogonal matrix of eigenvectors of a symmetric `A`, with `U Uᵀ = 1`, `Uᵀ U = 1`
and `A = U diag(specOf A) Uᵀ`. -/
private lemma gr_eig_decomp {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      A = U * diagonal (specOf A) * Uᵀ := by
  rw [specOf_eq hA]
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

/-- Conjugating a bilinear form by a real matrix `Q` rotates the test vectors by `Q`. -/
private lemma gr_testBilin_conj {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (B : Matrix ι ι ℂ)
    (v w : ι → ℝ) : testBilin v ((cplx Q)ᵀ * B * cplx Q) w = testBilin (Q *ᵥ v) B (Q *ᵥ w) := by
  have hc : ∀ u : ι → ℝ, cplx Q *ᵥ (fun t => (u t : ℂ)) = fun s => ((Q *ᵥ u) s : ℂ) := by
    intro u
    ext s
    simp [cplx, Matrix.mulVec, dotProduct]
  have hv : ∀ u : ι → ℝ, (fun s => (u s : ℂ)) ᵥ* (cplx Q)ᵀ = fun s => ((Q *ᵥ u) s : ℂ) := by
    intro u
    rw [Matrix.vecMul_transpose]
    exact hc u
  unfold testBilin
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hv, hc]

/-- A real matrix `Q` with `Qᵀ Q = 1` preserves the Euclidean norm of a test vector. -/
private lemma gr_testNorm_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Qᵀ * Q = 1) (v : ι → ℝ) : testNorm (Q *ᵥ v) = testNorm v := by
  unfold testNorm
  congr 1
  have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- `(P Q Pᵀ)⁻¹ = P Q⁻¹ Pᵀ` for a complex matrix `P` with `P Pᵀ = 1 = Pᵀ P` (no invertibility
of `Q` is needed). -/
private lemma gr_inv_conj {N : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} (hP : P * Pᵀ = 1)
    (hP' : Pᵀ * P = 1) (Q : Matrix (Fin N) (Fin N) ℂ) : (P * Q * Pᵀ)⁻¹ = P * Q⁻¹ * Pᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hP,
    Matrix.inv_eq_right_inv hP', Matrix.mul_assoc]

/-- A real orthogonal `U` is also orthogonal as a complex matrix: `U Uᵀ = 1 = Uᵀ U`. -/
private lemma gr_cplx_orth {N : ℕ} {U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1)
    (hUU' : Uᵀ * U = 1) :
    cplx U * (cplx U)ᵀ = 1 ∧ (cplx U)ᵀ * cplx U = 1 := by
  constructor
  · have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU
    simp only [cplx, Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_one _ (map_zero _) (map_one _)] at h ⊢
    exact h
  · have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => cplx M) hUU'
    simp only [cplx, Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_one _ (map_zero _) (map_one _)] at h ⊢
    exact h

/-- `(cplx (U B Uᵀ) − w)⁻¹ = U (cplx B − w)⁻¹ Uᵀ` for a real orthogonal `U`. -/
private lemma gr_resolvent_conj {N : ℕ} {U : Matrix (Fin N) (Fin N) ℝ} (hUU : U * Uᵀ = 1)
    (hUU' : Uᵀ * U = 1) (B : Matrix (Fin N) (Fin N) ℝ) (w : ℂ) :
    (cplx (U * B * Uᵀ) - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      cplx U * (cplx B - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * (cplx U)ᵀ := by
  obtain ⟨hP, hP'⟩ := gr_cplx_orth hUU hUU'
  have h1 : cplx (U * B * Uᵀ) - w • (1 : Matrix (Fin N) (Fin N) ℂ) =
      cplx U * (cplx B - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * (cplx U)ᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP]
    simp only [cplx, Matrix.map_mul, Matrix.transpose_map]
  rw [h1, gr_inv_conj hP hP']

/-- `m^W` of the diagonal matrix of eigenvalues equals `m^W` of `A`. -/
private lemma gr_mW_diag {N : ℕ} (a : Fin N → ℝ) (z : ℂ) :
    mW (specOf (diagonal a)) z = mW a z := by
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal a
  rw [he, mW_comp_perm]

private lemma gr_PsiW_diag {N : ℕ} (a : Fin N → ℝ) (z : ℂ) :
    PsiW (specOf (diagonal a)) z = PsiW a z := by
  unfold PsiW
  rw [gr_mW_diag]

/-- `G^W(A, M) = U G^W(D, Uᵀ M U) Uᵀ`. -/
private lemma gr_GW_eq {N : ℕ} {A U : Matrix (Fin N) (Fin N) ℝ} {l : Fin N → ℝ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal l * Uᵀ)
    (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    GW A M z = cplx U * GW (diagonal l) (Uᵀ * M * U) z * (cplx U)ᵀ := by
  unfold GW
  have h : M + A = U * (Uᵀ * M * U + diagonal l) * Uᵀ := by
    have : U * (Uᵀ * M * U + diagonal l) * Uᵀ = (U * Uᵀ) * M * (U * Uᵀ) + U * diagonal l * Uᵀ := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [this, hUU, Matrix.one_mul, Matrix.mul_one, ← hAU, add_comm]
  rw [h, gr_resolvent_conj hUU hUU']

/-- `Π^W(A) = U Π^W(D) Uᵀ`, with `m^W` evaluated at the spectrum of `A`. -/
private lemma gr_piW_eq {N : ℕ} {A U : Matrix (Fin N) (Fin N) ℝ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal (specOf A) * Uᵀ)
    (z : ℂ) :
    piW A z = cplx U * piW (diagonal (specOf A)) z * (cplx U)ᵀ := by
  have hc : ∀ c : ℂ, (cplx A - c • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      cplx U * (cplx (diagonal (specOf A)) - c • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *
        (cplx U)ᵀ := fun c => by
    have h := gr_resolvent_conj hUU hUU' (diagonal (specOf A)) c
    rwa [← hAU] at h
  unfold piW
  rw [gr_mW_diag]
  exact hc _

/-- `⟨v, (G^W(A, M) − Π^W(A)) w⟩ = ⟨Uᵀv, (G^W(D, Uᵀ M U) − Π^W(D)) Uᵀw⟩`. -/
private lemma gr_bilin_eq {N : ℕ} {A U : Matrix (Fin N) (Fin N) ℝ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal (specOf A) * Uᵀ)
    (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (v w : Fin N → ℝ) :
    testBilin v (GW A M z - piW A z) w =
      testBilin (Uᵀ *ᵥ v) (GW (diagonal (specOf A)) (Uᵀ * M * U) z -
        piW (diagonal (specOf A)) z) (Uᵀ *ᵥ w) := by
  have hQ : (cplx Uᵀ)ᵀ = cplx U := by simp [cplx, Matrix.transpose_map]
  have hQ' : cplx Uᵀ = (cplx U)ᵀ := by simp [cplx, Matrix.transpose_map]
  rw [gr_GW_eq hUU hUU' hAU, gr_piW_eq hUU hUU' hAU, ← Matrix.sub_mul, ← Matrix.mul_sub]
  have h := gr_testBilin_conj Uᵀ (GW (diagonal (specOf A)) (Uᵀ * M * U) z -
    piW (diagonal (specOf A)) z) v w
  rwa [hQ, hQ'] at h

/-- `N⁻¹ tr G^W(A, M) = N⁻¹ tr G^W(D, Uᵀ M U)`. -/
private lemma gr_mNW_eq {N : ℕ} {A U : Matrix (Fin N) (Fin N) ℝ}
    (hUU : U * Uᵀ = 1) (hUU' : Uᵀ * U = 1) (hAU : A = U * diagonal (specOf A) * Uᵀ)
    (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    mNW A M z = mNW (diagonal (specOf A)) (Uᵀ * M * U) z := by
  obtain ⟨_, hP'⟩ := gr_cplx_orth hUU hUU'
  unfold mNW
  rw [gr_GW_eq hUU hUU' hAU, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP',
    Matrix.one_mul]

/-- `M ↦ G^W(D, M)(z)` is measurable on all real matrices. -/
private lemma gr_measurable_GW {N : ℕ} (D : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Measurable fun M : Matrix (Fin N) (Fin N) ℝ => GW D M z := by
  have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℝ =>
      cplx (M + D) - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    refine Continuous.sub ?_ continuous_const
    exact (continuous_id.add continuous_const).matrix_map Complex.continuous_ofReal
  have hd : Measurable fun M : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (M + D) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := hc.matrix_det.measurable
  have ha : Continuous fun M : Matrix (Fin N) (Fin N) ℝ =>
      (cplx (M + D) - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := hc.matrix_adjugate
  refine Matrix.measurable_iff.2 fun i j => ?_
  unfold GW
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hd.inv.mul (ha.matrix_elem i j).measurable

private lemma gr_measurable_testBilin {α : Type*} [MeasurableSpace α] {N : ℕ}
    {f : α → Matrix (Fin N) (Fin N) ℂ} (hf : Measurable f) (v w : Fin N → ℝ) :
    Measurable fun x => testBilin v (f x) w := by
  unfold testBilin
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.const_mul (Finset.measurable_sum _ fun t _ => ?_) _
  exact (hf.eval_matrix (i := s) (j := t)).mul_const _

/-- `Uᵀ` is orthogonal when `U Uᵀ = 1 = Uᵀ U`. -/
private lemma gr_transpose_mem {N : ℕ} {U : Matrix (Fin N) (Fin N) ℝ} (hUU' : Uᵀ * U = 1) :
    Uᵀ ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  simpa using hUU'

private lemma gr_measurable_conj {N : ℕ} (O : Matrix (Fin N) (Fin N) ℝ) :
    Measurable fun X : Matrix (Fin N) (Fin N) ℝ => O * X * Oᵀ := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (Finset.measurable_sum _ fun l _ =>
    (measurable_id.eval_matrix (i := l) (j := k)).const_mul _).mul_const _

/-- Transport `D → A` by orthogonal invariance (`A = U D Uᵀ`), anisotropic law. -/
theorem goe_aniso_rotate {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {ε D : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W) {S : Set ℂ}
    (h : AnisotropicLawWAt N ε D (diagonal (specOf A)) W S) :
    AnisotropicLawWAt N ε D A W S := by
  obtain ⟨U, hUU, hUU', hAU⟩ := gr_eig_decomp hA
  intro z hz v w
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  have hYm : Measurable fun ω => Uᵀ * W ω * Uᵀᵀ := (gr_measurable_conj Uᵀ).comp hWm
  have hlaw := hW.map_conj (gr_transpose_mem hUU')
  have hξ : Measurable fun M : Matrix (Fin N) (Fin N) ℝ =>
      ‖testBilin (Uᵀ *ᵥ v) (GW (diagonal (specOf A)) M z - piW (diagonal (specOf A)) z)
        (Uᵀ *ᵥ w)‖ :=
    (gr_measurable_testBilin ((gr_measurable_GW _ z).sub_const _) _ _).norm
  have key := (domAt_comp_iff_of_map_eq (Y := fun ω => Uᵀ * W ω * Uᵀᵀ) (X := W)
    hYm.aemeasurable hWm.aemeasurable hlaw (N := N) (ε := ε) (D := D) hξ
    (ζ := fun _ => PsiW (specOf (diagonal (specOf A))) z * testNorm (Uᵀ *ᵥ v) *
      testNorm (Uᵀ *ᵥ w)) measurable_const).2 (h z hz (Uᵀ *ᵥ v) (Uᵀ *ᵥ w))
  have hn : ∀ u : Fin N → ℝ, testNorm (Uᵀ *ᵥ u) = testNorm u :=
    fun u => gr_testNorm_orth (by simpa using hUU) u
  simp only [hn, gr_PsiW_diag] at key
  simp only [Matrix.transpose_transpose] at key
  unfold DomAt at key ⊢
  simpa only [gr_bilin_eq hUU hUU' hAU, hn, gr_PsiW_diag] using key

/-- Transport `D → A` by orthogonal invariance, averaged law. -/
theorem goe_avg_rotate {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {N : ℕ} {ε D : ℝ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : IsGOE W) {S : Set ℂ} {Φ : ℂ → ℝ}
    (h : AveragedPhiLawWAt N ε D (diagonal (specOf A)) W S Φ) :
    AveragedPhiLawWAt N ε D A W S Φ := by
  obtain ⟨U, hUU, hUU', hAU⟩ := gr_eig_decomp hA
  intro z hz
  have hWm : Measurable W := Matrix.measurable_iff.2 hW.measurable
  have hYm : Measurable fun ω => Uᵀ * W ω * Uᵀᵀ := (gr_measurable_conj Uᵀ).comp hWm
  have hlaw := hW.map_conj (gr_transpose_mem hUU')
  have hmN : Measurable fun M : Matrix (Fin N) (Fin N) ℝ =>
      mNW (diagonal (specOf A)) M z := by
    unfold mNW
    refine Measurable.const_mul ?_ _
    unfold Matrix.trace
    exact Finset.measurable_sum _ fun i _ =>
      (gr_measurable_GW (diagonal (specOf A)) z).eval_matrix (i := i) (j := i)
  have hξ : Measurable fun M : Matrix (Fin N) (Fin N) ℝ =>
      ‖mNW (diagonal (specOf A)) M z - mW (specOf (diagonal (specOf A))) z‖ :=
    (hmN.sub_const _).norm
  have key := (domAt_comp_iff_of_map_eq (Y := fun ω => Uᵀ * W ω * Uᵀᵀ) (X := W)
    hYm.aemeasurable hWm.aemeasurable hlaw (N := N) (ε := ε) (D := D) hξ
    (ζ := fun _ => Φ z) measurable_const).2 (h z hz)
  simp only [Matrix.transpose_transpose] at key
  unfold ODomAt
  simpa only [gr_mNW_eq hUU hUU' hAU, gr_mW_diag] using key

/-! ## Nondegenerate instance `N = 2`, `A = aEx 2`, `W = goeW 2` -/

/-- Conditional instance (the law for the diagonal matrix is a binder): `A = aEx 2` is symmetric
and not diagonal, and `W = goeW 2` is a GOE matrix. -/
example {ε D : ℝ} {S : Set ℂ}
    (h : AnisotropicLawWAt 2 ε D (diagonal (specOf (aEx 2))) (goeW 2) S) :
    AnisotropicLawWAt 2 ε D (aEx 2) (goeW 2) S :=
  goe_aniso_rotate (aEx_isHermitian 2) (isGOE_goeW 2) h

/-- Conditional instance of the averaged transfer with control `Φ`. -/
example {ε D : ℝ} {S : Set ℂ} {Φ : ℂ → ℝ}
    (h : AveragedPhiLawWAt 2 ε D (diagonal (specOf (aEx 2))) (goeW 2) S Φ) :
    AveragedPhiLawWAt 2 ε D (aEx 2) (goeW 2) S Φ :=
  goe_avg_rotate (aEx_isHermitian 2) (isGOE_goeW 2) h

#print axioms goe_aniso_rotate
#print axioms goe_avg_rotate

end Anisotropic
