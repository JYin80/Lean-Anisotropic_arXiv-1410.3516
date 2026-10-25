import Anisotropic.Gaussian.Ensemble
import Anisotropic.Gaussian.Spectral
import Anisotropic.Framework.Domination

/-!
# Rotation invariance of the Gaussian ensemble

Section 6, proof of Proposition 6.1 from Lemma 6.2, equation (rotation of matrix): for a Gaussian
`X` with independent `N(0, 1/N)` entries and deterministic orthogonal `O_M`, `O_N`, the matrix
`O_M X O_Nᵀ` has the law of `X`. Contents:
* the law of the entries is the image of the standard Gaussian on the Euclidean space of entries
  under the scaling `N^{-1/2}`, and `A ↦ O_M A O_Nᵀ` is a linear isometry of that space for the
  Frobenius norm, so the law is invariant;
* the transfer of `DomAt` and `HighProbAt` statements between random variables with equal laws,
  and in particular from `X` to `O_M X O_Nᵀ`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! # Rotation invariance and the transfer of stochastic-domination statements -/

/-- The entries of `A` listed over `Fin K × Fin N`. -/
private def invariance_flat {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℝ) : Fin K × Fin N → ℝ :=
  fun p => A p.1 p.2

/-- The matrix with entries `x (i, μ)`. -/
private def invariance_unflat {K N : ℕ} (x : Fin K × Fin N → ℝ) : Matrix (Fin K) (Fin N) ℝ :=
  Matrix.of fun i μ => x (i, μ)

/-- `A ↦ O_M A O_Nᵀ` in the coordinates `Fin K × Fin N → ℝ`. -/
private def invariance_rotFlat {K N : ℕ} (OM : Matrix (Fin K) (Fin K) ℝ)
    (ON : Matrix (Fin N) (Fin N) ℝ) (x : Fin K × Fin N → ℝ) : Fin K × Fin N → ℝ :=
  invariance_flat (OM * invariance_unflat x * ONᵀ)

private lemma invariance_measurable_flat {K N : ℕ} :
    Measurable (invariance_flat (K := K) (N := N)) :=
  measurable_pi_iff.2 fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

private lemma invariance_measurable_unflat {K N : ℕ} :
    Measurable (invariance_unflat (K := K) (N := N)) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => measurable_pi_apply (i, μ)

private lemma invariance_measurable_rotFlat {K N : ℕ} (OM : Matrix (Fin K) (Fin K) ℝ)
    (ON : Matrix (Fin N) (Fin N) ℝ) : Measurable (invariance_rotFlat OM ON) := by
  refine measurable_pi_iff.2 fun p => ?_
  simp only [invariance_rotFlat, invariance_flat, invariance_unflat, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (Finset.measurable_sum _ fun k _ => (measurable_pi_apply (k, j)).const_mul _).mul_const _

/-- `∑_{i,μ} (O_M A O_Nᵀ)_{iμ}² = ∑_{i,μ} A_{iμ}²` for orthogonal `O_M`, `O_N`. -/
private lemma invariance_sum_sq_rot {K N : ℕ} {OM : Matrix (Fin K) (Fin K) ℝ}
    {ON : Matrix (Fin N) (Fin N) ℝ} (hOM : OM ∈ Matrix.orthogonalGroup (Fin K) ℝ)
    (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) (A : Matrix (Fin K) (Fin N) ℝ) :
    ∑ p : Fin K × Fin N, (OM * A * ONᵀ) p.1 p.2 ^ 2 = ∑ p : Fin K × Fin N, A p.1 p.2 ^ 2 := by
  have key : ∀ B : Matrix (Fin K) (Fin N) ℝ,
      ∑ p : Fin K × Fin N, B p.1 p.2 ^ 2 = (B * Bᵀ).trace := by
    intro B
    simp [Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply, sq]
  have hOM' : OMᵀ * OM = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin K) ℝ).1 hOM
  have hON' : ONᵀ * ON = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).1 hON
  rw [key, key]
  calc (OM * A * ONᵀ * (OM * A * ONᵀ)ᵀ).trace = (OM * (A * Aᵀ * OMᵀ)).trace := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ONᵀ ON, hON', Matrix.one_mul]
    _ = (A * Aᵀ * (OMᵀ * OM)).trace := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = (A * Aᵀ).trace := by rw [hOM', Matrix.mul_one]

/-- `A ↦ O_M A O_Nᵀ` as a linear map of the Euclidean space of entries. -/
private def invariance_rotLin {K N : ℕ} (OM : Matrix (Fin K) (Fin K) ℝ)
    (ON : Matrix (Fin N) (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin K × Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin K × Fin N) where
  toFun v := WithLp.toLp 2 (invariance_rotFlat OM ON v.ofLp)
  map_add' v w := by
    have h : invariance_unflat (v + w).ofLp =
        invariance_unflat v.ofLp + invariance_unflat w.ofLp := by
      ext i μ
      simp [invariance_unflat]
    ext p
    simp only [invariance_rotFlat, invariance_flat, h, Matrix.mul_add, Matrix.add_mul,
      PiLp.add_apply, Matrix.add_apply]
  map_smul' c v := by
    have h : invariance_unflat (c • v).ofLp = c • invariance_unflat v.ofLp := by
      ext i μ
      simp [invariance_unflat]
    ext p
    simp only [invariance_rotFlat, invariance_flat, h, Matrix.mul_smul, Matrix.smul_mul,
      PiLp.smul_apply, Matrix.smul_apply, RingHom.id_apply]

/-- `A ↦ O_M A O_Nᵀ` as a linear isometry of the Euclidean space of entries. -/
private def invariance_rotIso {K N : ℕ} {OM : Matrix (Fin K) (Fin K) ℝ}
    {ON : Matrix (Fin N) (Fin N) ℝ} (hOM : OM ∈ Matrix.orthogonalGroup (Fin K) ℝ)
    (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin K × Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K × Fin N) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := invariance_rotLin OM ON
      norm_map' := fun v => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
          EuclideanSpace.real_norm_sq_eq]
        exact invariance_sum_sq_rot hOM hON (invariance_unflat v.ofLp) } rfl

/-- The product of `N(0, 1/N)` laws is invariant under `A ↦ O_M A O_Nᵀ`. -/
private lemma invariance_pi_map_rotFlat {K N : ℕ} {OM : Matrix (Fin K) (Fin K) ℝ}
    {ON : Matrix (Fin N) (Fin N) ℝ} (hOM : OM ∈ Matrix.orthogonalGroup (Fin K) ℝ)
    (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    (Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹).map
        (invariance_rotFlat OM ON) =
      Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := by
  set c : ℝ := (Real.sqrt N)⁻¹
  let T : EuclideanSpace ℝ (Fin K × Fin N) → Fin K × Fin N → ℝ := fun v p => c * v.ofLp p
  have hTm : Measurable T := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (by fun_prop :
      Measurable fun v : EuclideanSpace ℝ (Fin K × Fin N) => v.ofLp p).const_mul c
  have hT : (Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹) =
      (stdGaussian (EuclideanSpace ℝ (Fin K × Fin N))).map T := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map hTm (PiLp.continuous_toLp 2 _).measurable]
    have h1 : T ∘ WithLp.toLp 2 = fun x (p : Fin K × Fin N) => (fun y : ℝ => c * y) (x p) := rfl
    rw [h1, Measure.pi_map_pi fun _ => (measurable_const_mul c).aemeasurable]
    congr 1
    funext p
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mk, mul_one, NNReal.coe_inv,
      NNReal.coe_natCast, c, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hcomm : invariance_rotFlat OM ON ∘ T = T ∘ invariance_rotIso hOM hON := by
    funext v
    ext p
    simp only [Function.comp_apply, T, invariance_rotIso, LinearIsometry.coe_toLinearIsometryEquiv,
      LinearIsometry.coe_mk, invariance_rotLin, LinearMap.coe_mk, AddHom.coe_mk,
      invariance_rotFlat, invariance_flat, invariance_unflat]
    have hs : (Matrix.of fun i μ => c * v.ofLp (i, μ)) =
        c • Matrix.of fun i μ => v.ofLp (i, μ) := by
      ext i μ
      simp
    rw [hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [hT, Measure.map_map (invariance_measurable_rotFlat OM ON) hTm, hcomm,
    ← Measure.map_map hTm (invariance_rotIso hOM hON).continuous.measurable, stdGaussian_map]

section Law

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Bi-orthogonal invariance ((rotation of matrix)): `O_M X O_Nᵀ` has the law of `X`. -/
theorem IsGaussianEnsemble.map_rotate {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) {OM : Matrix (Fin K) (Fin K) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin K) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    (ℙ : Measure Ω).map (fun ω => OM * X ω * ONᵀ) = (ℙ : Measure Ω).map X := by
  have hXm := hX.measurable_mat
  have hflat : (ℙ : Measure Ω).map (invariance_flat ∘ X) =
      Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := hX.map_entries
  have h1 : (fun ω => OM * X ω * ONᵀ) =
      invariance_unflat ∘ invariance_rotFlat OM ON ∘ invariance_flat ∘ X := rfl
  have h2 : X = invariance_unflat ∘ invariance_flat ∘ X := rfl
  rw [h1, ← Function.comp_assoc,
    ← Measure.map_map ((invariance_measurable_unflat).comp (invariance_measurable_rotFlat OM ON))
      (invariance_measurable_flat.comp hXm), hflat,
    ← Measure.map_map invariance_measurable_unflat (invariance_measurable_rotFlat OM ON),
    invariance_pi_map_rotFlat hOM hON, h2,
    ← Measure.map_map invariance_measurable_unflat (invariance_measurable_flat.comp hXm), hflat]

/-- A measurable matrix with the law of a Gaussian ensemble is a Gaussian ensemble. -/
private lemma invariance_of_map_eq {K N : ℕ} {X Y : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) (hYm : Measurable Y)
    (hYX : (ℙ : Measure Ω).map Y = (ℙ : Measure Ω).map X) : IsGaussianEnsemble Y := by
  have hmeas : ∀ i μ, Measurable fun ω => Y ω i μ := fun i μ =>
    (measurable_pi_apply μ).comp ((measurable_pi_apply i).comp hYm)
  have hjoint : (ℙ : Measure Ω).map (fun ω (p : Fin K × Fin N) => Y ω p.1 p.2) =
      Measure.pi fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹ := by
    have h : (fun ω (p : Fin K × Fin N) => Y ω p.1 p.2) = invariance_flat ∘ Y := rfl
    rw [h, ← Measure.map_map invariance_measurable_flat hYm, hYX,
      Measure.map_map invariance_measurable_flat hX.measurable_mat]
    exact hX.map_entries
  have hlaw : ∀ i μ, (ℙ : Measure Ω).map (fun ω => Y ω i μ) = gaussianReal 0 (N : ℝ≥0)⁻¹ := by
    intro i μ
    have h : (fun ω => Y ω i μ) =
        Function.eval (i, μ) ∘ fun ω (p : Fin K × Fin N) => Y ω p.1 p.2 := rfl
    rw [h, ← Measure.map_map (measurable_pi_apply (i, μ))
      (measurable_pi_iff.2 fun p => hmeas p.1 p.2), hjoint]
    exact (measurePreserving_eval (fun _ : Fin K × Fin N => gaussianReal 0 (N : ℝ≥0)⁻¹)
      (i, μ)).map_eq
  refine ⟨hmeas, ?_, hlaw⟩
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun (p : Fin K × Fin N) ω => Y ω p.1 p.2)
    fun p => (hmeas p.1 p.2).aemeasurable).2 ?_
  rw [hjoint]
  congr 1
  funext p
  exact (hlaw p.1 p.2).symm

/-- `O_M X O_Nᵀ` is again a Gaussian ensemble. -/
theorem IsGaussianEnsemble.rotate {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) {OM : Matrix (Fin K) (Fin K) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin K) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    IsGaussianEnsemble (fun ω => OM * X ω * ONᵀ) :=
  invariance_of_map_eq hX
    ((invariance_measurable_unflat.comp (invariance_measurable_rotFlat OM ON)).comp
      (invariance_measurable_flat.comp hX.measurable_mat)) (hX.map_rotate hOM hON)

end Law

section Transfer

variable {Ω : Type*} [MeasureSpace Ω]

/-- Transfer of `DomAt` between two random variables with the same law. -/
theorem domAt_comp_iff_of_map_eq {β : Type*} [MeasurableSpace β] {Y X : Ω → β}
    (hY : AEMeasurable Y ℙ) (hX : AEMeasurable X ℙ)
    (hlaw : (ℙ : Measure Ω).map Y = (ℙ : Measure Ω).map X) {N : ℕ} {ε D : ℝ} {ξ ζ : β → ℝ}
    (hξ : Measurable ξ) (hζ : Measurable ζ) :
    DomAt N ε D (fun ω => ξ (Y ω)) (fun ω => ζ (Y ω)) ↔
      DomAt N ε D (fun ω => ξ (X ω)) (fun ω => ζ (X ω)) := by
  have hE : MeasurableSet {b : β | (N : ℝ) ^ ε * ζ b < ξ b} :=
    measurableSet_lt (hζ.const_mul _) hξ
  unfold DomAt
  have h₁ : ℙ {ω | (N : ℝ) ^ ε * ζ (Y ω) < ξ (Y ω)} =
      (ℙ : Measure Ω).map Y {b : β | (N : ℝ) ^ ε * ζ b < ξ b} :=
    (Measure.map_apply_of_aemeasurable hY hE).symm
  have h₂ : ℙ {ω | (N : ℝ) ^ ε * ζ (X ω) < ξ (X ω)} =
      (ℙ : Measure Ω).map X {b : β | (N : ℝ) ^ ε * ζ b < ξ b} :=
    (Measure.map_apply_of_aemeasurable hX hE).symm
  rw [h₁, h₂, hlaw]

end Transfer

/-- `O_M X O_Nᵀ` is measurable when `X` is. -/
theorem measurable_rotate {Ω : Type*} [MeasurableSpace Ω] {K N : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : Measurable X) (OM : Matrix (Fin K) (Fin K) ℝ)
    (ON : Matrix (Fin N) (Fin N) ℝ) : Measurable fun ω => OM * X ω * ONᵀ := by
  have hX' : ∀ i k, Measurable fun ω => X ω i k := fun i k =>
    measurable_pi_iff.1 (measurable_pi_iff.1 hX i) k
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun μ => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (Finset.measurable_sum _ fun k _ => (hX' k j).const_mul _).mul_const _

section RotTransfer

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Transfer of `DomAt` from `X` to `O_M X O_Nᵀ`, Gaussian `X` ((rotation of matrix)). -/
theorem IsGaussianEnsemble.domAt_rotate {K N : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : IsGaussianEnsemble X) {OM : Matrix (Fin K) (Fin K) ℝ} {ON : Matrix (Fin N) (Fin N) ℝ}
    (hOM : OM ∈ Matrix.orthogonalGroup (Fin K) ℝ) (hON : ON ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    {n : ℕ} {ε D : ℝ} {ξ ζ : Matrix (Fin K) (Fin N) ℝ → ℝ} (hξ : Measurable ξ)
    (hζ : Measurable ζ) (h : DomAt n ε D (fun ω => ξ (X ω)) (fun ω => ζ (X ω))) :
    DomAt n ε D (fun ω => ξ (OM * X ω * ONᵀ)) (fun ω => ζ (OM * X ω * ONᵀ)) :=
  (domAt_comp_iff_of_map_eq (measurable_rotate hX.measurable_mat OM ON).aemeasurable
    hX.measurable_mat.aemeasurable (hX.map_rotate hOM hON) hξ hζ).2 h

end RotTransfer

/-- `map_rotate` at `K = N = 1`, `O_M = O_N = 1`. -/
example : (ℙ : Measure (GaussSpace 1 1)).map
      (fun ω => (1 : Matrix (Fin 1) (Fin 1) ℝ) * gaussX 1 1 ω * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) =
    (ℙ : Measure (GaussSpace 1 1)).map (gaussX 1 1) :=
  (gaussX_isGaussianEnsemble 1 1).map_rotate (one_mem _) (one_mem _)

end Anisotropic

#print axioms Anisotropic.IsGaussianEnsemble.map_rotate
#print axioms Anisotropic.IsGaussianEnsemble.rotate
#print axioms Anisotropic.domAt_comp_iff_of_map_eq
#print axioms Anisotropic.measurable_rotate
#print axioms Anisotropic.IsGaussianEnsemble.domAt_rotate
