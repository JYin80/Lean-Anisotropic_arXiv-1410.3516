module

public import Anisotropic.Comparison.Ensemble
public import Anisotropic.Comparison.Interpolation
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.EdgeUniv.CompareQ
public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.Reduction
public import Anisotropic.EdgeUniv.SmCount
public import Anisotropic.EdgeUniv.Swap
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Qdot.Defs
public import Anisotropic.Qdot.EdgeCompare
public import Anisotropic.Qdot.EdgeDefs
public import Anisotropic.Qdot.EdgeSwap
public import Anisotropic.Qdot.EdgeThird
public import Anisotropic.Qdot.LocalLaw

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The comparison of smooth functionals of the smoothed counts for `Q̇` -/

/-! ## Rescaling the smoothed count -/

open Polynomial in
private lemma ecm_charpoly_smul_eq_diagonal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    (c • A).charpoly = (diagonal (fun j => c * hA.eigenvalues j)).charpoly := by
  have hs := hA.spectral_theorem
  have h1 : c • A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      diagonal (fun j => c * hA.eigenvalues j) *
        star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply]
    have : diagonal (fun j => c * hA.eigenvalues j) =
        c • diagonal (fun j => hA.eigenvalues j) := by
      rw [← diagonal_smul]; rfl
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    simp
  rw [h1, charpoly_mul_comm, ← mul_assoc]
  simp

/-- The eigenvalues of `c A` are `c` times those of `A`, up to a permutation. -/
private lemma ecm_specOf_smul_perm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (c : ℝ) : ∃ e : Equiv.Perm (Fin n), specOf (c • A) = fun j => c * specOf A (e j) := by
  have hA' : (c • A).IsHermitian := hA.smul (IsSelfAdjoint.all c)
  have hD : (diagonal (fun j => c * hA.eigenvalues j)).IsHermitian := isHermitian_diagonal _
  have h1 : hA'.eigenvalues = hD.eigenvalues :=
    (hA'.eigenvalues_eq_eigenvalues_iff hD).2 (ecm_charpoly_smul_eq_diagonal hA c)
  obtain ⟨e, he⟩ := exists_perm_specOf_diagonal (fun j => c * hA.eigenvalues j)
  refine ⟨e, ?_⟩
  rw [specOf_eq hA', h1, ← specOf_eq hD, he, specOf_eq hA]
  rfl

/-- The rescaling identity `𝒳_{[E₁,E₂]}(c A) = 𝒳_{[E₁/c,E₂/c]}(A)` at smoothing scale `η/c` in
place of `η`, for `A` symmetric and `c ≠ 0` (the scaling of the argument `z` by `N/(N−1)` in
§11.2). -/
theorem smCount_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hc : c ≠ 0) (η E₁ E₂ : ℝ) :
    smCount (c • A) η E₁ E₂ = smCount A (η / c) (E₁ / c) (E₂ / c) := by
  obtain ⟨e, he⟩ := ecm_specOf_smul_perm hA c
  unfold smCount
  rw [← Equiv.sum_comp e (fun j => (Real.arctan ((E₂ / c - specOf A j) / (η / c)) -
    Real.arctan ((E₁ / c - specOf A j) / (η / c))) / Real.pi)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [he]
  have h : ∀ E : ℝ, (E - c * specOf A (e j)) / η = (E / c - specOf A (e j)) / (η / c) :=
    fun E => by
      rw [show E / c - specOf A (e j) = (E - c * specOf A (e j)) / c by field_simp,
        div_div_div_cancel_right₀ hc]
  rw [h, h]

/-- The rescaling identity at `A = diag(1, 2)`, `c = 2`, `η = 1`, window `[0, 3]`. -/
example : smCount ((2 : ℝ) • diagonal ![(1 : ℝ), 2]) 1 0 3 =
    smCount (diagonal ![(1 : ℝ), 2]) (1 / 2) 0 (3 / 2) := by
  rw [smCount_smul (isHermitian_diagonal _) two_ne_zero]
  norm_num

/-- `(X, y) ↦ G(X, y + iη)` is jointly continuous. -/
private lemma ecm_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
    (hη : 0 < η) :
    Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
      G Sig p.1 ((p.2 : ℂ) + η * Complex.I) := by
  have hX : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => cplx p.1 :=
    (continuous_id.matrix_map Complex.continuous_ofReal).comp continuous_fst
  have hXt : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ => cplx p.1ᵀ :=
    ((continuous_id.matrix_transpose).matrix_map Complex.continuous_ofReal).comp continuous_fst
  have hH : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
      H Sig p.1 ((p.2 : ℂ) + η * Complex.I) := by
    have h3 : Continuous fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
        -(((p.2 : ℂ) + η * Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      (((Complex.continuous_ofReal.comp continuous_snd).add continuous_const).smul
        continuous_const).neg
    exact continuous_const.matrix_fromBlocks hX hXt h3
  rw [continuous_iff_continuousAt]
  intro p
  have hu := (Matrix.isUnit_iff_isUnit_det _).1
    (H_isUnit hSig p.1 (z := (p.2 : ℂ) + η * Complex.I) (by simpa using hη))
  have hinv := continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)
  change ContinuousAt (fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
    (H Sig p.1 ((p.2 : ℂ) + η * Complex.I))⁻¹) p
  exact hinv.comp (f := fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
    H Sig p.1 ((p.2 : ℂ) + η * Complex.I)) hH.continuousAt

/-- `X ↦ 𝒳_{[E₁,E₂]}(Q_N(X))` is continuous. -/
private lemma ecm_continuous_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    {η : ℝ} (hη : 0 < η) (E₁ E₂ : ℝ) :
    Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => smCount (QN Sig Xm) η E₁ E₂ := by
  have he : (fun Xm : Matrix (Fin M) (Fin N) ℝ => smCount (QN Sig Xm) η E₁ E₂) =
      fun Xm => N / Real.pi * ∫ y in E₁..E₂, (mN Sig Xm (y + η * Complex.I)).im := by
    funext Xm
    exact smCount_eq_integral hSig Xm hη E₁ E₂
  rw [he]
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (Xm : Matrix (Fin M) (Fin N) ℝ) (y : ℝ) => (mN Sig Xm (y + η * Complex.I)).im) ?_
    E₁ E₂
  have hG := ecm_continuous_G (N := N) hSig hη
  have : Function.uncurry (fun (Xm : Matrix (Fin M) (Fin N) ℝ) (y : ℝ) =>
      (mN Sig Xm (y + η * Complex.I)).im) = fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
        ((N : ℂ)⁻¹ * ∑ ν, G Sig p.1 ((p.2 : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im := by
    funext p
    rfl
  rw [this]
  refine Complex.continuous_im.comp (continuous_const.mul (continuous_finsetSum _ fun ν _ => ?_))
  exact (continuous_apply_apply _ _).comp hG

private lemma ecm_continuous_ofCoord :
    Continuous (ofCoord : (Fin M × Fin N → ℝ) → Matrix (Fin M) (Fin N) ℝ) :=
  continuous_pi fun i => continuous_pi fun μ => continuous_apply (i, μ)

/-- The coordinate `α` of `x` replaced by `t`. -/
private lemma ecm_ofCoord_update (x : Fin M × Fin N → ℝ) (α : Fin M × Fin N) (t : ℝ) :
    ofCoord (Function.update x α t) = Xupd (ofCoord x) α.1 α.2 t := by
  funext j ν
  simp only [ofCoord, Xupd, Function.update_apply, Prod.ext_iff]

private lemma ecm_QN_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Xm (show Sig.IsHermitian from hSig.isHermitian)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-! ## Laws of the entries -/

private lemma ecm_gaussLaw_prob (N : ℕ) : IsProbabilityMeasure (gaussLaw N) := by
  unfold gaussLaw
  infer_instance

private lemma ecm_entryLaw_prob {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N) :
    IsProbabilityMeasure (entryLaw Y β) :=
  ⟨by simp [entryLaw, Measure.map_apply (hY.measurable β.1 β.2) MeasurableSet.univ]⟩

/-- Integrals against the law of one entry. -/
private lemma ecm_integral_entryLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ t, f t ∂(entryLaw Y β) = ∫ ω, f (Y ω β.1 β.2) :=
  integral_map (hY.measurable β.1 β.2).aemeasurable hf.aestronglyMeasurable

private lemma ecm_integrable_entryLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable fun ω => f (Y ω β.1 β.2)) :
    Integrable f (entryLaw Y β) :=
  (integrable_map_measure hf.aestronglyMeasurable (hY.measurable β.1 β.2).aemeasurable).2 hi

/-- `|y|^k = N^{-k/2} |√N y|^k`. -/
private lemma ecm_abs_pow_eq {N : ℕ} (hN : 1 ≤ N) (y : ℝ) (k : ℕ) :
    |y| ^ k = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * y| ^ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← mul_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn.le,
    ← Real.rpow_add hn]
  have : -(k : ℝ) / 2 + 1 / 2 * k = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-- `|E X_{iμ}^3| ≤ N^{-3/2} C_3`. -/
private lemma ecm_abs_third_le {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (hN : 1 ≤ N) (i : Fin K)
    (μ : Fin N) : |∫ ω, Y ω i μ ^ 3| ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * max (C 3) 0 := by
  rw [← Real.norm_eq_abs]
  have hi := hY.integrable_moment 3 i μ
  refine (norm_integral_le_of_norm_le (hi.const_mul ((N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)))
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_pow, ecm_abs_pow_eq hN]
  · rw [integral_const_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left ((hY.moment 3 i μ).trans (le_max_left _ _)) (by positivity)

/-! ## The sample space of `(X^θ, y₁, y₀)` -/

/-- The sample space of a triple `(x, y₁, y₀)` with law `μ ⊗ ν₁ ⊗ ν₀`. -/
private def EcmSpace (M N : ℕ) (_μ : Measure (Fin M × Fin N → ℝ)) (_ν₁ _ν₀ : Measure ℝ) : Type :=
  (Fin M × Fin N → ℝ) × (ℝ × ℝ)

private instance (μ : Measure (Fin M × Fin N → ℝ)) (ν₁ ν₀ : Measure ℝ) :
    MeasurableSpace (EcmSpace M N μ ν₁ ν₀) := Prod.instMeasurableSpace

private instance (μ : Measure (Fin M × Fin N → ℝ)) (ν₁ ν₀ : Measure ℝ) :
    MeasureSpace (EcmSpace M N μ ν₁ ν₀) := ⟨μ.prod (ν₁.prod ν₀)⟩

section EcmSpace

variable (μ : Measure (Fin M × Fin N → ℝ)) (ν₁ ν₀ : Measure ℝ) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₀]

private lemma ecm_prob : IsProbabilityMeasure (ℙ : Measure (EcmSpace M N μ ν₁ ν₀)) := by
  change IsProbabilityMeasure (μ.prod (ν₁.prod ν₀))
  infer_instance

omit [IsProbabilityMeasure μ] in
private lemma ecm_map_fst :
    (ℙ : Measure (EcmSpace M N μ ν₁ ν₀)).map (fun ω => (ω.1 : Fin M × Fin N → ℝ)) = μ := by
  change (μ.prod (ν₁.prod ν₀)).map Prod.fst = μ
  rw [Measure.map_fst_prod, measure_univ, one_smul]

private lemma ecm_integral_fst (g : (Fin M × Fin N → ℝ) → ℝ) :
    ∫ ω : EcmSpace M N μ ν₁ ν₀, g ω.1 = ∫ x, g x ∂μ := by
  change ∫ q, g q.1 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_fst, probReal_univ, one_smul]

private lemma ecm_integral_y₁ (g : ℝ → ℝ) :
    ∫ ω : EcmSpace M N μ ν₁ ν₀, g ω.2.1 = ∫ t, g t ∂ν₁ := by
  change ∫ q, (fun r : ℝ × ℝ => g r.1) q.2 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_snd (f := fun r : ℝ × ℝ => g r.1), probReal_univ, one_smul,
    integral_fun_fst (f := g), probReal_univ, one_smul]

private lemma ecm_integral_y₀ (g : ℝ → ℝ) :
    ∫ ω : EcmSpace M N μ ν₁ ν₀, g ω.2.2 = ∫ t, g t ∂ν₀ := by
  change ∫ q, (fun r : ℝ × ℝ => g r.2) q.2 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_snd (f := fun r : ℝ × ℝ => g r.2), probReal_univ, one_smul,
    integral_fun_snd (f := g), probReal_univ, one_smul]

private lemma ecm_integrable_y₁ {g : ℝ → ℝ} (hg : Integrable g ν₁) :
    Integrable fun ω : EcmSpace M N μ ν₁ ν₀ => g ω.2.1 := by
  change Integrable (fun q => (fun r : ℝ × ℝ => g r.1) q.2) (μ.prod (ν₁.prod ν₀))
  exact (hg.comp_fst ν₀).comp_snd μ

private lemma ecm_integrable_y₀ {g : ℝ → ℝ} (hg : Integrable g ν₀) :
    Integrable fun ω : EcmSpace M N μ ν₁ ν₀ => g ω.2.2 := by
  change Integrable (fun q => (fun r : ℝ × ℝ => g r.2) q.2) (μ.prod (ν₁.prod ν₀))
  exact (hg.comp_snd ν₁).comp_snd μ

omit [IsProbabilityMeasure μ] in
/-- `E g(X^θ, y₁) = ∫ g d(μ ⊗ ν₁)`. -/
private lemma ecm_integral_pair₁ {g : (Fin M × Fin N → ℝ) × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω : EcmSpace M N μ ν₁ ν₀, g (ω.1, ω.2.1) = ∫ q, g q ∂(μ.prod ν₁) := by
  have hm : (μ.prod (ν₁.prod ν₀)).map (Prod.map id Prod.fst) = μ.prod ν₁ := by
    rw [← Measure.map_prod_map μ (ν₁.prod ν₀) measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hm, integral_map (measurable_id.prodMap measurable_fst).aemeasurable
    hg.aestronglyMeasurable]
  rfl

omit [IsProbabilityMeasure μ] in
/-- `E g(X^θ, y₀) = ∫ g d(μ ⊗ ν₀)`. -/
private lemma ecm_integral_pair₀ {g : (Fin M × Fin N → ℝ) × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω : EcmSpace M N μ ν₁ ν₀, g (ω.1, ω.2.2) = ∫ q, g q ∂(μ.prod ν₀) := by
  have hm : (μ.prod (ν₁.prod ν₀)).map (Prod.map id Prod.snd) = μ.prod ν₀ := by
    rw [← Measure.map_prod_map μ (ν₁.prod ν₀) measurable_id measurable_snd, Measure.map_id,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hm, integral_map (measurable_id.prodMap measurable_snd).aemeasurable
    hg.aestronglyMeasurable]
  rfl

private lemma ecm_indep_fst_snd :
    IndepFun (fun ω : EcmSpace M N μ ν₁ ν₀ => (ω.1 : Fin M × Fin N → ℝ))
      (fun ω => (ω.2 : ℝ × ℝ)) := by
  change IndepFun (Prod.fst : (Fin M × Fin N → ℝ) × (ℝ × ℝ) → _) Prod.snd (μ.prod (ν₁.prod ν₀))
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp only [Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, Measure.map_snd_prod,
    measure_univ, one_smul]

end EcmSpace

/-- The entry assumptions pass to `X ∘ f` for a measure-preserving `f`. -/
private lemma ecm_entry_transfer {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')] {f : Ω' → Ω}
    (hf : Measurable f) (hmap : (ℙ : Measure Ω').map f = ℙ) {C : ℕ → ℝ} {K : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X) :
    EntryAssumption C fun ω' => X (f ω') := by
  have key : ∀ g : ℝ → ℝ, Continuous g → ∀ i μ,
      ∫ ω', g (X (f ω') i μ) = ∫ ω, g (X ω i μ) := fun g hg i μ => by
    have h := integral_map (μ := (ℙ : Measure Ω')) hf.aemeasurable (f := fun ω => g (X ω i μ))
      (hg.measurable.comp (hX.measurable i μ)).aestronglyMeasurable
    rw [hmap] at h
    exact h.symm
  have hmeasX : ∀ β : Fin K × Fin N, Measurable fun ω => X ω β.1 β.2 :=
    fun β => hX.measurable β.1 β.2
  refine ⟨fun i μ => (hX.measurable i μ).comp hf, ?_, fun i μ => ?_, fun i μ => ?_,
    fun q i μ => ?_, fun q i μ => ?_⟩
  · have hm' : ∀ β : Fin K × Fin N, AEMeasurable (fun ω' => X (f ω') β.1 β.2) ℙ :=
      fun β => ((hmeasX β).comp hf).aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map hm']
    have h := (iIndepFun_iff_map_fun_eq_pi_map (fun β => (hmeasX β).aemeasurable)).1 hX.indep
    have hg : Measurable fun ω (β : Fin K × Fin N) => X ω β.1 β.2 := measurable_pi_iff.2 hmeasX
    have e1 : (ℙ : Measure Ω').map (fun ω' (β : Fin K × Fin N) => X (f ω') β.1 β.2) =
        (ℙ : Measure Ω).map (fun ω (β : Fin K × Fin N) => X ω β.1 β.2) := by
      rw [← hmap, Measure.map_map hg hf]; rfl
    have e2 : ∀ β : Fin K × Fin N, (ℙ : Measure Ω').map (fun ω' => X (f ω') β.1 β.2) =
        (ℙ : Measure Ω).map (fun ω => X ω β.1 β.2) := fun β => by
      rw [← hmap, Measure.map_map (hmeasX β) hf]; rfl
    rw [e1, h]
    simp_rw [e2]
  · exact (key (fun t => t) continuous_id i μ).trans (hX.mean i μ)
  · exact (key (fun t => t ^ 2) (by fun_prop) i μ).trans (hX.var i μ)
  · have hc : Continuous fun t : ℝ => |Real.sqrt N * t| ^ q := by fun_prop
    have h := hX.integrable_moment q i μ
    have h1 : Integrable (fun t : ℝ => |Real.sqrt N * t| ^ q)
        ((ℙ : Measure Ω').map fun ω => X (f ω) i μ) := by
      rw [show (fun ω => X (f ω) i μ) = (fun ω => X ω i μ) ∘ f from rfl,
        ← Measure.map_map (hX.measurable i μ) hf, hmap]
      exact (integrable_map_measure hc.aestronglyMeasurable (hX.measurable i μ).aemeasurable).2 h
    exact (integrable_map_measure hc.aestronglyMeasurable
      ((hX.measurable i μ).comp hf).aemeasurable).1 h1
  · exact (key (fun t => |Real.sqrt N * t| ^ q) (by fun_prop) i μ).trans_le (hX.moment q i μ)

/-- The mean, variance and moments of the law of one entry. -/
private lemma ecm_law_props {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N) :
    (∫ t, t ∂(entryLaw Y β) = 0) ∧ (∫ t, t ^ 2 ∂(entryLaw Y β) = 1 / (N : ℝ)) ∧
      ∀ p : ℕ, Integrable (fun t : ℝ => |Real.sqrt N * t| ^ p) (entryLaw Y β) ∧
        ∫ t, |Real.sqrt N * t| ^ p ∂(entryLaw Y β) ≤ C p :=
  ⟨(ecm_integral_entryLaw hY β continuous_id).trans (hY.mean β.1 β.2),
    (ecm_integral_entryLaw hY β (f := fun t => t ^ 2) (by fun_prop)).trans (hY.var β.1 β.2),
    fun p => ⟨ecm_integrable_entryLaw hY β (by fun_prop) (hY.integrable_moment p β.1 β.2),
      (ecm_integral_entryLaw hY β (f := fun t => |Real.sqrt N * t| ^ p) (by fun_prop)).trans_le
        (hY.moment p β.1 β.2)⟩⟩

/-! ## Exponent arithmetic -/

/-- `Q ≤ N^a` once `⌈Q^{1/a}⌉ ≤ N`. -/
private lemma ecm_le_rpow {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) {N : ℕ}
    (h : ⌈Q ^ a⁻¹⌉₊ ≤ N) : Q ≤ (N : ℝ) ^ a := by
  have h1 : Q ^ a⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  calc Q = (Q ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hQ ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hQ _) h1 ha.le

/-- The third-order total `N^{-3/2} N^{4/3+21ε}` and the swap total `M N N^{-7/3+20ε}`, with
`M ≤ τ⁻¹ N`, are together at most `N^{-(1/6-25ε)}` once the constants are below `N^{4ε}`. -/
private lemma ecm_final {N M : ℕ} (hN : 1 ≤ N) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ)
    (hM : (M : ℝ) ≤ τ⁻¹ * N) {KT KS c3 Cb : ℝ} (hKS : 0 ≤ KS) (hCb : 0 ≤ Cb)
    (hA : KT * c3 / 6 + τ⁻¹ * KS ≤ (N : ℝ) ^ (4 * ε)) :
    1 / 6 * (KT * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3) * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε)) +
        ((M : ℝ) * N) * (KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε)) ≤
      Cb * (N : ℝ) ^ (-(1 / 6 - 25 * ε)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set P := (N : ℝ) ^ (-(1 / 6 - 25 * ε)) with hP
  set Q := (N : ℝ) ^ (-(4 * ε)) with hQ
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNp.le _
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hNp.le _
  have e1 : (N : ℝ) ^ (-(3 : ℝ) / 2) * (N : ℝ) ^ (4 / 3 + 21 * ε) = P * Q := by
    rw [hP, hQ, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
    ring_nf
  have e2 : (N : ℝ) * N * (N : ℝ) ^ (-7 / 3 + 20 * ε) = P * (N : ℝ) ^ (-1 / 6 - 5 * ε) := by
    have hNN : (N : ℝ) * N = (N : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [hNN, hP, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
    ring_nf
  have h3 : (N : ℝ) ^ (-1 / 6 - 5 * ε) ≤ Q :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hQ1 : Q * (N : ℝ) ^ (4 * ε) = 1 := by
    rw [hQ, ← Real.rpow_add hNp]
    simp
  have hX0 : 0 ≤ (N : ℝ) ^ (-7 / 3 + 20 * ε) := Real.rpow_nonneg hNp.le _
  have t1 : 1 / 6 * (KT * ((N : ℝ) ^ (-(3 : ℝ) / 2) * c3) * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε)) =
      (KT * c3 / 6) * Cb * (P * Q) := by
    rw [← e1]; ring
  have t2 : ((M : ℝ) * N) * (KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε)) ≤
      (τ⁻¹ * KS) * Cb * (P * Q) := by
    have hτi : 0 ≤ τ⁻¹ := inv_nonneg.2 hτ.le
    calc ((M : ℝ) * N) * (KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε))
        ≤ (τ⁻¹ * N * N) * (KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε)) := by
          gcongr
      _ = (τ⁻¹ * KS) * Cb * ((N : ℝ) * N * (N : ℝ) ^ (-7 / 3 + 20 * ε)) := by ring
      _ = (τ⁻¹ * KS) * Cb * (P * (N : ℝ) ^ (-1 / 6 - 5 * ε)) := by rw [e2]
      _ ≤ (τ⁻¹ * KS) * Cb * (P * Q) := by gcongr
  rw [t1]
  calc (KT * c3 / 6) * Cb * (P * Q) + ((M : ℝ) * N) * (KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε))
      ≤ (KT * c3 / 6 + τ⁻¹ * KS) * (Cb * P * Q) := by nlinarith
    _ ≤ (N : ℝ) ^ (4 * ε) * (Cb * P * Q) := by gcongr
    _ = Cb * P * (Q * (N : ℝ) ^ (4 * ε)) := by ring
    _ = Cb * P := by rw [hQ1, mul_one]

/-- `0 ≤ a_k ≤ 2τ⁻¹(1 + τ⁻¹)` at a regular edge of a model. -/
private lemma ecm_edgeVal_le {Ω : Type*} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} {k : ℕ} (hτ : 0 < τ)
    (hm : IsModel τ C M N Sig X) (hk : RegularEdge τ N (specOf Sig) k) :
    |edgeVal N (specOf Sig) k| ≤ 2 * τ⁻¹ * (1 + τ⁻¹) := by
  have hda : DensityAssumptions τ N (specOf Sig) := hm.diagModel_specOf.densityAssumptions hτ
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := hm.ratio_ge
      simp [h0] at this
      linarith
    · exact h0
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso
      have := hm.ratio_ge
      simp [h0] at this
      linarith
    · exact h0
  have hS : (posVals (specOf Sig)).Nonempty := by
    refine ⟨specOf Sig ⟨0, hM⟩, ?_⟩
    simp only [posVals, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [specOf_eq hm.sigma.posDef.isHermitian]
    exact hm.sigma.posDef.eigenvalues_pos _
  have h := edgeVal_mem_Icc N (specOf Sig) hda.nonneg hN hS hτ hda.phi_lower hda.phi_upper
    hda.bound_Sigma hk.1 hk.2.1
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The rescaled smoothing scale: `η_N/2 ≤ η_{N−1}(N−1)/N ≤ η_N`, `η_N = N^{−2/3−9ε}`. -/
private lemma ecm_eta_range {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    etaE N ε / 2 ≤ etaE (N - 1) ε / ((N : ℝ) / (N - 1)) ∧
      etaE (N - 1) ε / ((N : ℝ) / (N - 1)) ≤ etaE N ε := by
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hn0 : (0 : ℝ) < N := by linarith
  have hm0 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set β : ℝ := 1 / 3 - 9 * ε with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have e1 : etaE (N - 1) ε / ((N : ℝ) / (N - 1)) = ((N : ℝ) - 1) ^ β / N := by
    unfold etaE
    rw [hm, hβ, show (1 / 3 - 9 * ε : ℝ) = (-2 / 3 - 9 * ε) + 1 by ring,
      Real.rpow_add_one hm0.ne']
    field_simp
  have e2 : etaE N ε = (N : ℝ) ^ β / N := by
    unfold etaE
    rw [hβ, ← Real.rpow_sub_one hn0.ne']
    congr 1
    ring
  rw [e1, e2]
  have hle : ((N : ℝ) - 1) ^ β ≤ (N : ℝ) ^ β := Real.rpow_le_rpow hm0.le (by linarith) hβ0
  have h2 : (N : ℝ) ^ β ≤ 2 * ((N : ℝ) - 1) ^ β := by
    calc (N : ℝ) ^ β ≤ (2 * ((N : ℝ) - 1)) ^ β := Real.rpow_le_rpow hn0.le (by linarith) hβ0
      _ = 2 ^ β * ((N : ℝ) - 1) ^ β := Real.mul_rpow (by norm_num) hm0.le
      _ ≤ 2 * ((N : ℝ) - 1) ^ β := by
        gcongr
        calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
          _ = 2 := Real.rpow_one 2
  constructor
  · rw [show (N : ℝ) ^ β / N / 2 = (N : ℝ) ^ β / 2 / N by ring]
    gcongr
    linarith
  · gcongr

/-- A point within `2 (N−1)^{−2/3+ε}` of `ȧ`, divided by `N/(N−1)`, lies within `3 N^{−2/3+ε}` of
`a`, once `|ȧ − a| ≤ C₁/N`, `|a| ≤ K_a` and `2|C₁| + K_a ≤ N^{1/3}`. -/
private lemma ecm_window {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) {a ad x C₁ Ka : ℝ}
    (hpd : |ad - a| ≤ C₁ / N) (ha : |a| ≤ Ka) (hK : 2 * |C₁| + Ka ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hx : |x - ad| ≤ 2 * ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + ε)) :
    |x / ((N : ℝ) / (N - 1)) - a| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) := by
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hm] at hx
  have hn0 : (0 : ℝ) < N := by linarith
  have hm0 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set n : ℝ := (N : ℝ) with hn
  set w : ℝ := n ^ (-2 / 3 + ε) with hwdef
  set w' : ℝ := (n - 1) ^ (-2 / 3 + ε) with hw'def
  have hw : w' * (n - 1) / n ≤ w := by
    have e1 : w' * (n - 1) = (n - 1) ^ (1 / 3 + ε) := by
      rw [hw'def, show (1 / 3 + ε : ℝ) = (-2 / 3 + ε) + 1 by ring, Real.rpow_add_one hm0.ne']
    have e2 : w = n ^ (1 / 3 + ε) / n := by
      rw [hwdef, ← Real.rpow_sub_one hn0.ne']
      congr 1
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hm0.le (by linarith) (by linarith)) hn0.le
  have hKn : (2 * |C₁| + Ka) / n ≤ w := by
    calc (2 * |C₁| + Ka) / n ≤ n ^ (1 / 3 : ℝ) / n := div_le_div_of_nonneg_right hK hn0.le
      _ = n ^ (-2 / 3 : ℝ) := by
        rw [← Real.rpow_sub_one hn0.ne']
        norm_num
      _ ≤ w := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hc : x / (n / (n - 1)) - a = (x - ad) * (n - 1) / n - ad / n + (ad - a) := by
    field_simp
    ring
  have hC : C₁ / n ≤ |C₁| / n := div_le_div_of_nonneg_right (le_abs_self _) hn0.le
  have hC' : |C₁| / n ≤ |C₁| := div_le_self (abs_nonneg _) (by linarith)
  have hadabs : |ad| ≤ Ka + |C₁| := by
    have h1 : ad = a + (ad - a) := by ring
    have h2 := abs_add_le a (ad - a)
    rw [← h1] at h2
    linarith
  have t1 : |(x - ad) * (n - 1) / n| ≤ 2 * w := by
    rw [abs_div, abs_mul, abs_of_pos hm0, abs_of_pos hn0]
    calc |x - ad| * (n - 1) / n ≤ 2 * w' * (n - 1) / n := by gcongr
      _ = 2 * (w' * (n - 1) / n) := by ring
      _ ≤ 2 * w := by linarith [hw]
  have t2 : |ad / n| ≤ (Ka + |C₁|) / n := by
    rw [abs_div, abs_of_pos hn0]
    exact div_le_div_of_nonneg_right hadabs hn0.le
  have e3 : (Ka + |C₁|) / n + |C₁| / n = (2 * |C₁| + Ka) / n := by ring
  rw [hc]
  obtain ⟨u1, u2⟩ := abs_le.1 t1
  obtain ⟨v1, v2⟩ := abs_le.1 t2
  obtain ⟨r1, r2⟩ := abs_le.1 hpd
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith


/-! ## The comparison step -/

/-- The comparison input of the reduction for `Q̇` at the partner edge, with `N − 1` samples: smooth functionals of the smoothed
counts of `(−1)^{k'+1} Q̇` for `X` and for Gaussian `X` differ by `C_b (N−1)^{−(1/6 − 25ε)}`. -/
theorem smoothComparable_dot (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      SmoothComparable (N - 1)
        (edgeSign (edgePartner N (specOf Sig) k) *
          edgeVal (N - 1) (specOf Sig) (edgePartner N (specOf Sig) k)) ε (1 / 6 - 25 * ε) l
        (fun ω => edgeSign (edgePartner N (specOf Sig) k) • QdotN Sig (X ω))
        (fun ω => edgeSign (edgePartner N (specOf Sig) k) • QdotN Sig (gaussX M N ω)) := by
  obtain ⟨KS, NS, hS⟩ := dot_smF_swap τ (momMax C) l ε hτ hε hε1
  obtain ⟨KT, NT, hT⟩ := dot_smT_third_sum τ (momMax C) l ε hτ hε hε1
  obtain ⟨C₁, NP, hP⟩ := edgePartner_spec τ hτ
  set A : ℝ := max KT 0 * max (C 3) 0 / 6 + τ⁻¹ * max KS 0 with hA
  have hA0 : 0 ≤ A := by
    have := inv_nonneg.2 hτ.le
    have h1 := le_max_right KT 0
    have h2 := le_max_right (C 3) 0
    have h3 := le_max_right KS 0
    positivity
  set Ka : ℝ := 2 * τ⁻¹ * (1 + τ⁻¹) with hKa
  have hKw0 : 0 ≤ 2 * |C₁| + Ka := by
    have := inv_nonneg.2 hτ.le
    positivity
  refine ⟨max (max (max NS NT) (max ⌈A ^ (4 * ε)⁻¹⌉₊ 2))
    (max NP ⌈(2 * |C₁| + Ka) ^ (1 / 3 : ℝ)⁻¹⌉₊), ?_⟩
  intro N hN Ω _ _ M Sig X k hX hk F Cb hF hFb E hE
  have hNa := le_of_max_le_left hN
  have hNb := le_of_max_le_right hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hNa)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN2
  have hNS : NS ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hNa)
  have hNT : NT ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hNa)
  have hNA : ⌈A ^ (4 * ε)⁻¹⌉₊ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hNa)
  have hNP : NP ≤ N := le_of_max_le_left hNb
  have hNK : ⌈(2 * |C₁| + Ka) ^ (1 / 3 : ℝ)⁻¹⌉₊ ≤ N := le_of_max_le_right hNb
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hm0 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hSig := hX.sigma.posDef
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hFB : ∀ x, |F x| ≤ Cb := fun x => by
    have := hFb 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  -- the partner edge
  have hda : DensityAssumptions τ N (specOf Sig) := hX.diagModel_specOf.densityAssumptions hτ
  obtain ⟨-, hpd, -⟩ := hP N hNP M (specOf Sig) hda k hk
  have ha := ecm_edgeVal_le hτ hX hk
  have hK : 2 * |C₁| + Ka ≤ (N : ℝ) ^ (1 / 3 : ℝ) := ecm_le_rpow hKw0 (by norm_num) hNK
  set k' := edgePartner N (specOf Sig) k with hk'
  set a := edgeVal N (specOf Sig) k with ha'
  set ad := edgeVal (N - 1) (specOf Sig) k' with had
  set c : ℝ := (N : ℝ) / (N - 1) with hc
  have hc0 : 0 < c := div_pos hNp hm0
  set η' : ℝ := etaE (N - 1) ε / c with hη'
  obtain ⟨hηl, hηu⟩ := ecm_eta_range hN2 hε hε1
  have hη : 0 < η' := lt_of_lt_of_le (by
    have : 0 < etaE N ε := Real.rpow_pos_of_pos hNp _
    linarith) hηl
  set w' : ℝ := ((N - 1 : ℕ) : ℝ) ^ (-2 / 3 + ε) with hw'
  have hw'0 : 0 ≤ w' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hwin : ∀ x, |x - ad| ≤ 2 * w' → |x / c - a| ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε) :=
    fun x hx => ecm_window hN2 hε hpd ha hK hx
  -- the rescaling by `c = N/(N−1)` and the mirror for `k'` even
  obtain ⟨Ea, Eb, hW, hid⟩ : ∃ Ea Eb : Fin l → ℝ, EdgeWindows N a ε Ea Eb ∧
      ∀ B : Matrix (Fin N) (Fin N) ℝ, B.IsHermitian →
        (fun j => smCount (edgeSign k' • (c • B)) (etaE (N - 1) ε) (E j)
          (edgeEL (N - 1) (edgeSign k' * ad) ε)) =
          fun j => smCount B η' (Ea j) (Eb j) := by
    rcases Nat.mod_two_eq_zero_or_one k' with h2 | h2
    · have hs : edgeSign k' = -1 := by simp [edgeSign, h2]
      refine ⟨fun _ => (ad - 2 * w') / c, fun j => -E j / c, fun j => ⟨?_, ?_⟩, fun B hB => ?_⟩
      · refine hwin _ ?_
        rw [show ad - 2 * w' - ad = -(2 * w') by ring, abs_neg, abs_of_nonneg (by positivity)]
      · refine hwin _ ?_
        have h := hE j
        rw [hs] at h
        rw [show -E j - ad = -(E j - -1 * ad) by ring, abs_neg]
        linarith
      · funext j
        rw [hs, neg_one_smul, smCount_neg (hB.smul (IsSelfAdjoint.all c)),
          smCount_smul hB hc0.ne']
        congr 2
        unfold edgeEL
        ring
    · have hs : edgeSign k' = 1 := by simp [edgeSign, h2]
      refine ⟨fun j => E j / c, fun _ => edgeEL (N - 1) ad ε / c, fun j => ⟨?_, ?_⟩,
        fun B hB => ?_⟩
      · refine hwin _ ?_
        have h := hE j
        rw [hs, one_mul] at h
        linarith
      · refine hwin _ ?_
        rw [show edgeEL (N - 1) ad ε - ad = 2 * w' by unfold edgeEL; ring,
          abs_of_nonneg (by positivity)]
      · funext j
        rw [hs, one_smul, one_mul, smCount_smul hB hc0.ne']
  have e₁ : (fun ω => F (fun j => smCount (edgeSign k' • QdotN Sig (X ω)) (etaE (N - 1) ε) (E j)
      (edgeEL (N - 1) (edgeSign k' * ad) ε))) =
        fun ω => smF F Sig (Xdot (X ω)) η' Ea Eb :=
    funext fun ω => by
      rw [show QdotN Sig (X ω) = c • QN Sig (Xdot (X ω)) from rfl,
        hid _ (ecm_QN_isHermitian hSig _)]
      rfl
  have e₀ : (fun ω => F (fun j => smCount (edgeSign k' • QdotN Sig (gaussX M N ω))
      (etaE (N - 1) ε) (E j) (edgeEL (N - 1) (edgeSign k' * ad) ε))) =
        fun ω => smF F Sig (Xdot (gaussX M N ω)) η' Ea Eb :=
    funext fun ω => by
      rw [show QdotN Sig (gaussX M N ω) = c • QN Sig (Xdot (gaussX M N ω)) from rfl,
        hid _ (ecm_QN_isHermitian hSig _)]
      rfl
  beta_reduce
  rw [e₁, e₀]
  -- the laws of `X`, `X⁰` and the function `Φ = F ∘ 𝒳 ∘ Xdot ∘ ofCoord`
  set ρ₀ : Fin M × Fin N → Measure ℝ := fun _ => gaussLaw N with hρ₀
  set ρ₁ : Fin M × Fin N → Measure ℝ := entryLaw X with hρ₁
  have : IsProbabilityMeasure (gaussLaw N) := ecm_gaussLaw_prob N
  have : ∀ α, IsProbabilityMeasure (ρ₀ α) := fun _ => ecm_gaussLaw_prob N
  have : ∀ α, IsProbabilityMeasure (ρ₁ α) := ecm_entryLaw_prob hX.entries
  set Φ : (Fin M × Fin N → ℝ) → ℝ := fun x => smF F Sig (Xdot (ofCoord x)) η' Ea Eb with hΦ
  have hXdc : Continuous (Xdot : Matrix (Fin M) (Fin N) ℝ → Matrix (Fin M) (Fin N) ℝ) :=
    continuous_id.matrix_mul continuous_const
  have hΦc : Continuous Φ := hF.continuous.comp (continuous_pi fun j =>
    (ecm_continuous_smCount hSig hη (Ea j) (Eb j)).comp (hXdc.comp ecm_continuous_ofCoord))
  have hΦm : Measurable Φ := hΦc.measurable
  have hΦi : ∀ (ν : Measure (Fin M × Fin N → ℝ)) [IsFiniteMeasure ν], Integrable Φ ν :=
    fun ν _ => Integrable.of_bound hΦm.aestronglyMeasurable Cb
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFB _)
  have hvert : ∀ u, Integrable Φ (vertexLaw ρ₀ ρ₁ u) := fun u => by
    have : ∀ α, IsProbabilityMeasure (if u α then ρ₁ α else ρ₀ α) := fun α => by
      split <;> infer_instance
    have : IsProbabilityMeasure (vertexLaw ρ₀ ρ₁ u) := by unfold vertexLaw; infer_instance
    exact hΦi _
  have hX1 : ∫ ω, smF F Sig (Xdot (X ω)) η' Ea Eb = ∫ x, Φ x ∂(Measure.pi ρ₁) := by
    have hmeasX : ∀ β : Fin M × Fin N, Measurable fun ω => X ω β.1 β.2 :=
      fun β => hX.entries.measurable β.1 β.2
    have hg1 : Measurable fun ω (β : Fin M × Fin N) => X ω β.1 β.2 := measurable_pi_iff.2 hmeasX
    have hlaw : Measure.pi ρ₁ =
        (ℙ : Measure Ω).map (fun ω (β : Fin M × Fin N) => X ω β.1 β.2) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun β => (hmeasX β).aemeasurable)).1 hX.entries.indep]
      rfl
    rw [hlaw, integral_map hg1.aemeasurable hΦm.aestronglyMeasurable]
    rfl
  have hX0 : ∫ ω, smF F Sig (Xdot (gaussX M N ω)) η' Ea Eb = ∫ x, Φ x ∂(Measure.pi ρ₀) := rfl
  rw [hX1, hX0, interpol hΦm hvert]
  -- the bound for every `θ ∈ [0, 1]`
  set m3 : Fin M → Fin N → ℝ := fun i μ => ∫ ω, X ω i μ ^ 3 with hm3
  set S : ℝ := (N : ℝ) ^ (-(3 : ℝ) / 2) * max (C 3) 0 with hSdef
  set B : ℝ := 1 / 6 * (max KT 0 * S * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε)) +
      ((M : ℝ) * N) * (max KS 0 * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε)) with hB
  have hθ : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |∑ α, ((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
      ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)))| ≤ B := by
    intro θ hθ
    have hmixP : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
      fun β => isProbabilityMeasure_mixMeasure _ _ _
    have hIP : IsProbabilityMeasure (interpLaw θ ρ₀ ρ₁) := by unfold interpLaw; infer_instance
    have : IsProbabilityMeasure (ℙ : Measure (InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁)) := hIP
    have hEθ : EntryAssumption (momMax C) (Ω := InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) ofCoord :=
      entryAssumption_interp hX.entries hN1 hθ.1 hθ.2
    have hmodθ : IsModel τ (momMax C) M N Sig (Ω := InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁)
        ofCoord := ⟨hX.ratio_ge, hX.ratio_le, hEθ, hX.sigma⟩
    have hAt : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (α : Fin M × Fin N),
        IsProbabilityMeasure (interpLawAt θ ρ₀ ρ₁ α ρ) := by
      intro ρ _ α
      have : ∀ β', IsProbabilityMeasure
          (Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ β') := fun β' => by
        by_cases h : β' = α
        · rw [h, Function.update_self]; infer_instance
        · rw [Function.update_of_ne h]; exact hmixP β'
      unfold interpLawAt
      infer_instance
    set T : Fin M × Fin N → ℝ := fun α => ∫ x, dotLen N ^ 3 *
      smT 3 F Sig (Xdot (ofCoord x) * dotRefl N α.2) η' Ea Eb α.1 α.2
        ((Xdot (ofCoord x) * dotRefl N α.2) α.1 α.2) ∂(interpLaw θ ρ₀ ρ₁) with hTdef
    have h3 : |∑ i, ∑ μ, m3 i μ * T (i, μ)| ≤ KT * S * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε) :=
      hT N hNT (Ω := InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) M Sig ofCoord k m3 S F Cb Ea Eb η'
        hmodθ hk (fun i μ => ecm_abs_third_le hX.entries hN1 i μ) hF hFb hW hηl hηu
    have hG : EntryAssumption (momMax C) (gaussX M N) :=
      ((gaussX_isGaussianEnsemble M N).entryAssumption hN1).mono fun q => le_max_right _ _
    -- one entry: the swap of `y₁ ∼ law(X_α)` against `y₀ ∼ N(0, 1/N)` in `X^θ`
    have hent : ∀ α : Fin M × Fin N, |((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
        ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) - m3 α.1 α.2 / 6 * T α| ≤
          KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε) := by
      intro α
      have : IsProbabilityMeasure (ρ₁ α) := ecm_entryLaw_prob hX.entries α
      have : IsProbabilityMeasure (ρ₀ α) := ecm_gaussLaw_prob N
      have : IsProbabilityMeasure
          (ℙ : Measure (EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α))) := ecm_prob _ _ _
      have hfm : Measurable fun ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          (ω.1 : InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) := measurable_fst
      have hE' := ecm_entry_transfer (Ω := InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) hfm
        (by exact ecm_map_fst (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) hEθ
      have hmod' : IsModel τ (momMax C) M N Sig
          (fun ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
            ofCoord (ω.1 : InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁)) :=
        ⟨hX.ratio_ge, hX.ratio_le, hE', hX.sigma⟩
      have hind := ecm_indep_fst_snd (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)
      have hind1 : IndepFun (fun ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          ofCoord (ω.1 : Fin M × Fin N → ℝ)) (fun ω => (ω.2.1 : ℝ)) :=
        hind.comp ecm_continuous_ofCoord.measurable measurable_fst
      have hind0 : IndepFun (fun ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          ofCoord (ω.1 : Fin M × Fin N → ℝ)) (fun ω => (ω.2.2 : ℝ)) :=
        hind.comp ecm_continuous_ofCoord.measurable measurable_snd
      have hlawG : ρ₀ α = entryLaw (gaussX M N) α :=
        ((gaussX_isGaussianEnsemble M N).law α.1 α.2).symm
      obtain ⟨m1, v1, p1⟩ := ecm_law_props (hX.entries.mono fun q => le_max_left (C q) _) α
      obtain ⟨m0, v0, p0⟩ := ecm_law_props hG α
      rw [← hlawG] at m0 v0 p0
      have hmean1 : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) = 0 :=
        (ecm_integral_y₁ _ _ _ (fun t => t)).trans m1
      have hmean0 : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) = 0 :=
        (ecm_integral_y₀ _ _ _ (fun t => t)).trans m0
      have hvar1 : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) ^ 2 =
          1 / (N : ℝ) := (ecm_integral_y₁ _ _ _ (fun t => t ^ 2)).trans v1
      have hvar0 : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) ^ 2 =
          1 / (N : ℝ) := (ecm_integral_y₀ _ _ _ (fun t => t ^ 2)).trans v0
      have hmom1 : ∀ p : ℕ, Integrable (fun ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          |Real.sqrt N * (ω.2.1 : ℝ)| ^ p) ∧
          ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), |Real.sqrt N * (ω.2.1 : ℝ)| ^ p ≤
            momMax C p := fun p =>
        ⟨ecm_integrable_y₁ _ _ _ (p1 p).1,
          (ecm_integral_y₁ _ _ _ (fun t => |Real.sqrt N * t| ^ p)).trans_le (p1 p).2⟩
      have hmom0 : ∀ p : ℕ, Integrable (fun ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          |Real.sqrt N * (ω.2.2 : ℝ)| ^ p) ∧
          ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), |Real.sqrt N * (ω.2.2 : ℝ)| ^ p ≤
            momMax C p := fun p =>
        ⟨ecm_integrable_y₀ _ _ _ (p0 p).1,
          (ecm_integral_y₀ _ _ _ (fun t => |Real.sqrt N * t| ^ p)).trans_le (p0 p).2⟩
      have hsw := hS N hNS (Ω := EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) M Sig
        (fun ω => ofCoord (ω.1 : Fin M × Fin N → ℝ)) k (fun ω => (ω.2.1 : ℝ))
        (fun ω => (ω.2.2 : ℝ)) α.1 α.2 F Cb Ea Eb η' hmod' hk hind1 hind0
        (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd) hmean1 hmean0
        hvar1 hvar0 hmom1 hmom0 hF hFb hW hηl hηu
      have e1 : ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α)) =
          ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smF F Sig (Xdot (Xupd (ofCoord (ω.1 : Fin M × Fin N → ℝ)) α.1 α.2 (ω.2.1 : ℝ)))
              η' Ea Eb := by
        have := hAt (ρ₁ α) α
        rw [integral_interpLawAt_eq α (ρ₁ α) hΦm (hΦi _), ← ecm_integral_pair₁
          (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) (g := fun q => Φ (Function.update q.1 α q.2))
          (hΦm.comp measurable_update')]
        simp only [hΦ, ecm_ofCoord_update]
      have e0 : ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)) =
          ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smF F Sig (Xdot (Xupd (ofCoord (ω.1 : Fin M × Fin N → ℝ)) α.1 α.2 (ω.2.2 : ℝ)))
              η' Ea Eb := by
        have := hAt (ρ₀ α) α
        rw [integral_interpLawAt_eq α (ρ₀ α) hΦm (hΦi _), ← ecm_integral_pair₀
          (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) (g := fun q => Φ (Function.update q.1 α q.2))
          (hΦm.comp measurable_update')]
        simp only [hΦ, ecm_ofCoord_update]
      have a1 : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) ^ 3 =
          ∫ t, t ^ 3 ∂(ρ₁ α) := ecm_integral_y₁ _ _ _ (fun t => t ^ 3)
      have a1' : ∫ t, t ^ 3 ∂(ρ₁ α) = m3 α.1 α.2 :=
        ecm_integral_entryLaw hX.entries α (f := fun t => t ^ 3) (by fun_prop)
      have a0 : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) ^ 3 =
          ∫ t, t ^ 3 ∂(ρ₀ α) := ecm_integral_y₀ _ _ _ (fun t => t ^ 3)
      have a0' : ∫ t, t ^ 3 ∂(ρ₀ α) = 0 := by
        rw [hlawG]
        exact (ecm_integral_entryLaw hG α (f := fun t => t ^ 3) (by fun_prop)).trans
          (zeroThird_gaussX M N α.1 α.2)
      have c1 : (∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) ^ 3) -
          (∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) ^ 3) =
            m3 α.1 α.2 := by
        rw [a1, a1', a0, a0', sub_zero]
      have tT : ∫ ω : EcmSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
          dotLen N ^ 3 * smT 3 F Sig (Xdot (ofCoord (ω.1 : Fin M × Fin N → ℝ)) * dotRefl N α.2)
            η' Ea Eb α.1 α.2
            ((Xdot (ofCoord (ω.1 : Fin M × Fin N → ℝ)) * dotRefl N α.2) α.1 α.2) = T α :=
        ecm_integral_fst (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)
          (fun x => dotLen N ^ 3 * smT 3 F Sig (Xdot (ofCoord x) * dotRefl N α.2) η' Ea Eb
            α.1 α.2 ((Xdot (ofCoord x) * dotRefl N α.2) α.1 α.2))
      rw [e1, e0, ← c1, ← tT]
      exact hsw
    -- the sum over the entries
    have hNp' : 0 ≤ (N : ℝ) := hNp.le
    have hS0 : 0 ≤ S := mul_nonneg (Real.rpow_nonneg hNp' _) (le_max_right _ _)
    have hY0 : 0 ≤ (N : ℝ) ^ (4 / 3 + 21 * ε) := Real.rpow_nonneg hNp' _
    have hX0 : 0 ≤ (N : ℝ) ^ (-7 / 3 + 20 * ε) := Real.rpow_nonneg hNp' _
    have hsplit : ∑ α, ((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
        ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) =
        1 / 6 * ∑ i, ∑ μ, m3 i μ * T (i, μ) + ∑ α, (((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
          ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) - m3 α.1 α.2 / 6 * T α) := by
      have e : 1 / 6 * ∑ i, ∑ μ, m3 i μ * T (i, μ) =
          ∑ α : Fin M × Fin N, m3 α.1 α.2 / 6 * T α := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        ring
      rw [e, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have t1 : |1 / 6 * ∑ i, ∑ μ, m3 i μ * T (i, μ)| ≤
        1 / 6 * (max KT 0 * S * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
      refine mul_le_mul_of_nonneg_left (h3.trans ?_) (by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hS0) hCb) hY0
    have t2 : |∑ α, (((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
          ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) - m3 α.1 α.2 / 6 * T α)| ≤
        ((M : ℝ) * N) * (max KS 0 * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun α _ => (hent α).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left KS 0) hCb) hX0)).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, le_refl]
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add t1 t2)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B)
    (f := fun θ => ∑ α, ((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
      ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))))
    (fun θ hθ' => by
      rw [Set.uIoc_of_le zero_le_one] at hθ'
      rw [Real.norm_eq_abs]
      exact hθ θ ⟨hθ'.1.le, hθ'.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  refine hint.trans ?_
  have hM : (M : ℝ) ≤ τ⁻¹ * N := by
    have := hX.ratio_le
    rwa [div_le_iff₀ hNp] at this
  refine (ecm_final hN1 hε hτ hM (le_max_right KS 0) hCb
    (ecm_le_rpow hA0 (by positivity) hNA)).trans ?_
  -- from `N^{−c₁}` to `(N−1)^{−c₁}`
  refine mul_le_mul_of_nonneg_left ?_ hCb
  rw [hm]
  exact Real.rpow_le_rpow_of_nonpos hm0 (by linarith) (by linarith)

/-- The comparison input at the Marchenko–Pastur point `Σ = I_n`, `N = 2n`, Rademacher against
Gaussian entries, `τ = 1/5`, `k = 1`, with every hypothesis of `smoothComparable_dot`
discharged. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    SmoothComparable (2 * n - 1)
      (edgeSign (edgePartner (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) *
        edgeVal (2 * n - 1) (specOf (1 : Matrix (Fin n) (Fin n) ℝ))
          (edgePartner (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1))
      (1 / 200) (1 / 6 - 25 * (1 / 200)) 1
      (fun ω => edgeSign (edgePartner (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) •
        QdotN (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω))
      (fun ω => edgeSign (edgePartner (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1) •
        QdotN (1 : Matrix (Fin n) (Fin n) ℝ) (gaussX n (2 * n) ω)) := by
  obtain ⟨N₀, h⟩ := smoothComparable_dot (1 / 5) (fun _ => 1) 1 (1 / 200) (by norm_num)
    (by norm_num) le_rfl
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hk : RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
    rw [specOf_one_eq]; exact regularEdge_mp hn
  exact h (2 * n) hN n 1 (radXn n) 1 (isModel_radXn hn) hk

#print axioms smCount_smul
#print axioms smoothComparable_dot

end Anisotropic
