module

public import Anisotropic.Comparison.Ensemble
public import Anisotropic.Comparison.Interpolation
public import Anisotropic.Density.Count
public import Anisotropic.Density.Critical
public import Anisotropic.EdgeUniv.Defs
public import Anisotropic.EdgeUniv.Reduction
public import Anisotropic.EdgeUniv.Swap
public import Anisotropic.EdgeUniv.ThirdSum
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.Framework.Domination
public import Anisotropic.Framework.Model
public import Anisotropic.Instances.MarchenkoPastur
public import Anisotropic.Instances.Models
public import Anisotropic.Probability.NormBound.GaussianLower
public import Anisotropic.Rigidity.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The comparison of smooth functionals of the smoothed counts for `Q` -/

/-! ## Continuity of the smoothed counts in the entries -/

/-- `(X, y) ↦ G(X, y + iη)` is jointly continuous. -/
private lemma cmpQ_continuous_G {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef) {η : ℝ}
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
private lemma cmpQ_continuous_smCount {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
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
  have hG := cmpQ_continuous_G (N := N) hSig hη
  have : Function.uncurry (fun (Xm : Matrix (Fin M) (Fin N) ℝ) (y : ℝ) =>
      (mN Sig Xm (y + η * Complex.I)).im) = fun p : Matrix (Fin M) (Fin N) ℝ × ℝ =>
        ((N : ℂ)⁻¹ * ∑ ν, G Sig p.1 ((p.2 : ℂ) + η * Complex.I) (Sum.inr ν) (Sum.inr ν)).im := by
    funext p
    rfl
  rw [this]
  refine Complex.continuous_im.comp (continuous_const.mul (continuous_finsetSum _ fun ν _ => ?_))
  exact (continuous_apply_apply _ _).comp hG

private lemma cmpQ_continuous_ofCoord :
    Continuous (ofCoord : (Fin M × Fin N → ℝ) → Matrix (Fin M) (Fin N) ℝ) :=
  continuous_pi fun i => continuous_pi fun μ => continuous_apply (i, μ)

/-- The coordinate `α` of `x` replaced by `t`. -/
private lemma cmpQ_ofCoord_update (x : Fin M × Fin N → ℝ) (α : Fin M × Fin N) (t : ℝ) :
    ofCoord (Function.update x α t) = Xupd (ofCoord x) α.1 α.2 t := by
  funext j ν
  simp only [ofCoord, Xupd, Function.update_apply, Prod.ext_iff]

private lemma cmpQ_QN_isHermitian {Sig : Matrix (Fin M) (Fin M) ℝ} (hSig : Sig.PosDef)
    (Xm : Matrix (Fin M) (Fin N) ℝ) : (QN Sig Xm).IsHermitian := by
  have := Matrix.isHermitian_conjTranspose_mul_mul Xm (show Sig.IsHermitian from hSig.isHermitian)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-! ## Laws of the entries -/

private lemma cmpQ_gaussLaw_prob (N : ℕ) : IsProbabilityMeasure (gaussLaw N) := by
  unfold gaussLaw
  infer_instance

private lemma cmpQ_entryLaw_prob {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N) :
    IsProbabilityMeasure (entryLaw Y β) :=
  ⟨by simp [entryLaw, Measure.map_apply (hY.measurable β.1 β.2) MeasurableSet.univ]⟩

/-- Integrals against the law of one entry. -/
private lemma cmpQ_integral_entryLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ t, f t ∂(entryLaw Y β) = ∫ ω, f (Y ω β.1 β.2) :=
  integral_map (hY.measurable β.1 β.2).aemeasurable hf.aestronglyMeasurable

private lemma cmpQ_integrable_entryLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable fun ω => f (Y ω β.1 β.2)) :
    Integrable f (entryLaw Y β) :=
  (integrable_map_measure hf.aestronglyMeasurable (hY.measurable β.1 β.2).aemeasurable).2 hi

/-- `|y|^k = N^{-k/2} |√N y|^k`. -/
private lemma cmpQ_abs_pow_eq {N : ℕ} (hN : 1 ≤ N) (y : ℝ) (k : ℕ) :
    |y| ^ k = (N : ℝ) ^ (-(k : ℝ) / 2) * |Real.sqrt N * y| ^ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← mul_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn.le,
    ← Real.rpow_add hn]
  have : -(k : ℝ) / 2 + 1 / 2 * k = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-- `|E X_{iμ}^3| ≤ N^{-3/2} C_3`. -/
private lemma cmpQ_abs_third_le {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (hN : 1 ≤ N) (i : Fin K)
    (μ : Fin N) : |∫ ω, Y ω i μ ^ 3| ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) * max (C 3) 0 := by
  rw [← Real.norm_eq_abs]
  have hi := hY.integrable_moment 3 i μ
  refine (norm_integral_le_of_norm_le (hi.const_mul ((N : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)))
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_pow, cmpQ_abs_pow_eq hN]
  · rw [integral_const_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left ((hY.moment 3 i μ).trans (le_max_left _ _)) (by positivity)

/-! ## The sample space of `(X^θ, y₁, y₀)` -/

/-- The sample space of a triple `(x, y₁, y₀)` with law `μ ⊗ ν₁ ⊗ ν₀`. -/
private def CmpSpace (M N : ℕ) (_μ : Measure (Fin M × Fin N → ℝ)) (_ν₁ _ν₀ : Measure ℝ) : Type :=
  (Fin M × Fin N → ℝ) × (ℝ × ℝ)

private instance (μ : Measure (Fin M × Fin N → ℝ)) (ν₁ ν₀ : Measure ℝ) :
    MeasurableSpace (CmpSpace M N μ ν₁ ν₀) := Prod.instMeasurableSpace

private instance (μ : Measure (Fin M × Fin N → ℝ)) (ν₁ ν₀ : Measure ℝ) :
    MeasureSpace (CmpSpace M N μ ν₁ ν₀) := ⟨μ.prod (ν₁.prod ν₀)⟩

section CmpSpace

variable (μ : Measure (Fin M × Fin N → ℝ)) (ν₁ ν₀ : Measure ℝ) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₀]

private lemma cmpQ_prob : IsProbabilityMeasure (ℙ : Measure (CmpSpace M N μ ν₁ ν₀)) := by
  change IsProbabilityMeasure (μ.prod (ν₁.prod ν₀))
  infer_instance

omit [IsProbabilityMeasure μ] in
private lemma cmpQ_map_fst :
    (ℙ : Measure (CmpSpace M N μ ν₁ ν₀)).map (fun ω => (ω.1 : Fin M × Fin N → ℝ)) = μ := by
  change (μ.prod (ν₁.prod ν₀)).map Prod.fst = μ
  rw [Measure.map_fst_prod, measure_univ, one_smul]

private lemma cmpQ_integral_fst (g : (Fin M × Fin N → ℝ) → ℝ) :
    ∫ ω : CmpSpace M N μ ν₁ ν₀, g ω.1 = ∫ x, g x ∂μ := by
  change ∫ q, g q.1 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_fst, probReal_univ, one_smul]

private lemma cmpQ_integral_y₁ (g : ℝ → ℝ) :
    ∫ ω : CmpSpace M N μ ν₁ ν₀, g ω.2.1 = ∫ t, g t ∂ν₁ := by
  change ∫ q, (fun r : ℝ × ℝ => g r.1) q.2 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_snd (f := fun r : ℝ × ℝ => g r.1), probReal_univ, one_smul,
    integral_fun_fst (f := g), probReal_univ, one_smul]

private lemma cmpQ_integral_y₀ (g : ℝ → ℝ) :
    ∫ ω : CmpSpace M N μ ν₁ ν₀, g ω.2.2 = ∫ t, g t ∂ν₀ := by
  change ∫ q, (fun r : ℝ × ℝ => g r.2) q.2 ∂(μ.prod (ν₁.prod ν₀)) = _
  rw [integral_fun_snd (f := fun r : ℝ × ℝ => g r.2), probReal_univ, one_smul,
    integral_fun_snd (f := g), probReal_univ, one_smul]

private lemma cmpQ_integrable_y₁ {g : ℝ → ℝ} (hg : Integrable g ν₁) :
    Integrable fun ω : CmpSpace M N μ ν₁ ν₀ => g ω.2.1 := by
  change Integrable (fun q => (fun r : ℝ × ℝ => g r.1) q.2) (μ.prod (ν₁.prod ν₀))
  exact (hg.comp_fst ν₀).comp_snd μ

private lemma cmpQ_integrable_y₀ {g : ℝ → ℝ} (hg : Integrable g ν₀) :
    Integrable fun ω : CmpSpace M N μ ν₁ ν₀ => g ω.2.2 := by
  change Integrable (fun q => (fun r : ℝ × ℝ => g r.2) q.2) (μ.prod (ν₁.prod ν₀))
  exact (hg.comp_snd ν₁).comp_snd μ

omit [IsProbabilityMeasure μ] in
/-- `E g(X^θ, y₁) = ∫ g d(μ ⊗ ν₁)`. -/
private lemma cmpQ_integral_pair₁ {g : (Fin M × Fin N → ℝ) × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω : CmpSpace M N μ ν₁ ν₀, g (ω.1, ω.2.1) = ∫ q, g q ∂(μ.prod ν₁) := by
  have hm : (μ.prod (ν₁.prod ν₀)).map (Prod.map id Prod.fst) = μ.prod ν₁ := by
    rw [← Measure.map_prod_map μ (ν₁.prod ν₀) measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod, measure_univ, one_smul]
  rw [← hm, integral_map (measurable_id.prodMap measurable_fst).aemeasurable
    hg.aestronglyMeasurable]
  rfl

omit [IsProbabilityMeasure μ] in
/-- `E g(X^θ, y₀) = ∫ g d(μ ⊗ ν₀)`. -/
private lemma cmpQ_integral_pair₀ {g : (Fin M × Fin N → ℝ) × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω : CmpSpace M N μ ν₁ ν₀, g (ω.1, ω.2.2) = ∫ q, g q ∂(μ.prod ν₀) := by
  have hm : (μ.prod (ν₁.prod ν₀)).map (Prod.map id Prod.snd) = μ.prod ν₀ := by
    rw [← Measure.map_prod_map μ (ν₁.prod ν₀) measurable_id measurable_snd, Measure.map_id,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hm, integral_map (measurable_id.prodMap measurable_snd).aemeasurable
    hg.aestronglyMeasurable]
  rfl

private lemma cmpQ_indep_fst_snd :
    IndepFun (fun ω : CmpSpace M N μ ν₁ ν₀ => (ω.1 : Fin M × Fin N → ℝ))
      (fun ω => (ω.2 : ℝ × ℝ)) := by
  change IndepFun (Prod.fst : (Fin M × Fin N → ℝ) × (ℝ × ℝ) → _) Prod.snd (μ.prod (ν₁.prod ν₀))
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp only [Prod.mk.eta, Measure.map_id', Measure.map_fst_prod, Measure.map_snd_prod,
    measure_univ, one_smul]

end CmpSpace

/-- The entry assumptions pass to `X ∘ f` for a measure-preserving `f`. -/
private lemma cmpQ_entry_transfer {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
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
private lemma cmpQ_law_props {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {Y : Ω → Matrix (Fin K) (Fin N) ℝ} (hY : EntryAssumption C Y) (β : Fin K × Fin N) :
    (∫ t, t ∂(entryLaw Y β) = 0) ∧ (∫ t, t ^ 2 ∂(entryLaw Y β) = 1 / (N : ℝ)) ∧
      ∀ p : ℕ, Integrable (fun t : ℝ => |Real.sqrt N * t| ^ p) (entryLaw Y β) ∧
        ∫ t, |Real.sqrt N * t| ^ p ∂(entryLaw Y β) ≤ C p :=
  ⟨(cmpQ_integral_entryLaw hY β continuous_id).trans (hY.mean β.1 β.2),
    (cmpQ_integral_entryLaw hY β (f := fun t => t ^ 2) (by fun_prop)).trans (hY.var β.1 β.2),
    fun p => ⟨cmpQ_integrable_entryLaw hY β (by fun_prop) (hY.integrable_moment p β.1 β.2),
      (cmpQ_integral_entryLaw hY β (f := fun t => |Real.sqrt N * t| ^ p) (by fun_prop)).trans_le
        (hY.moment p β.1 β.2)⟩⟩

/-! ## Exponent arithmetic -/

/-- `Q ≤ N^a` once `⌈Q^{1/a}⌉ ≤ N`. -/
private lemma cmpQ_le_rpow {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) {N : ℕ}
    (h : ⌈Q ^ a⁻¹⌉₊ ≤ N) : Q ≤ (N : ℝ) ^ a := by
  have h1 : Q ^ a⁻¹ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h)
  calc Q = (Q ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hQ ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hQ _) h1 ha.le

/-- The third-order total `N^{-3/2} N^{4/3+21ε}` and the swap total `M N N^{-7/3+20ε}`, with
`M ≤ τ⁻¹ N`, are together at most `N^{-(1/6-25ε)}` once the constants are below `N^{4ε}`. -/
private lemma cmpQ_final {N M : ℕ} (hN : 1 ≤ N) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ)
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

/-! ## The comparison step -/

/-- The comparison step for `Q`: (`SmoothComparable`) for `(-1)^{k+1} Q_N` with `X` against
Gaussian `X`, with `c₁ = 1/6 - 25ε`. -/
theorem smoothComparable_Q (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 200) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ) (k : ℕ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      SmoothComparable N (edgeSign k * edgeVal N (specOf Sig) k) ε (1 / 6 - 25 * ε) l
        (fun ω => edgeSign k • QN Sig (X ω)) (fun ω => edgeSign k • QN Sig (gaussX M N ω)) := by
  obtain ⟨KS, NS, hS⟩ := smF_swap τ (momMax C) l ε hτ hε hε1
  obtain ⟨KT, NT, hT⟩ := smT_third_sum τ (momMax C) l ε hτ hε hε1
  set A : ℝ := max KT 0 * max (C 3) 0 / 6 + τ⁻¹ * max KS 0 with hA
  have hA0 : 0 ≤ A := by
    have := inv_nonneg.2 hτ.le
    have h1 := le_max_right KT 0
    have h2 := le_max_right (C 3) 0
    have h3 := le_max_right KS 0
    positivity
  refine ⟨max (max NS NT) (max ⌈A ^ (4 * ε)⁻¹⌉₊ 1), ?_⟩
  intro N hN Ω _ _ M Sig X k hX hk F Cb hF hFb E hE
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNS : NS ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNT : NT ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNA : ⌈A ^ (4 * ε)⁻¹⌉₊ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hSig := hX.sigma.posDef
  have hη : 0 < etaE N ε := Real.rpow_pos_of_pos hNp _
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hFB : ∀ x, |F x| ≤ Cb := fun x => by
    have := hFb 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  set a := edgeVal N (specOf Sig) k with ha
  set w : ℝ := (N : ℝ) ^ (-2 / 3 + ε) with hw
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos hNp _).le
  -- the mirror `k` even: `𝒳_{[E, E_L]}(-Q) = 𝒳_{[-E_L, -E]}(Q)`
  obtain ⟨Ea, Eb, hW, hid⟩ : ∃ Ea Eb : Fin l → ℝ, EdgeWindows N a ε Ea Eb ∧
      ∀ B : Matrix (Fin N) (Fin N) ℝ, B.IsHermitian →
        (fun j => smCount (edgeSign k • B) (etaE N ε) (E j) (edgeEL N (edgeSign k * a) ε)) =
          fun j => smCount B (etaE N ε) (Ea j) (Eb j) := by
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · have hs : edgeSign k = -1 := by simp [edgeSign, h2]
      refine ⟨fun _ => a - 2 * w, fun j => -E j, fun j => ⟨?_, ?_⟩, fun B hB => ?_⟩
      · have e : a - 2 * w - a = -(2 * w) := by ring
        rw [e, abs_neg, abs_of_nonneg (by positivity)]
        linarith
      · have h := hE j
        rw [hs] at h
        have e : -E j - a = -(E j - -1 * a) := by ring
        rw [e, abs_neg]
        linarith
      · funext j
        rw [hs, neg_one_smul, smCount_neg hB]
        congr 1
        unfold edgeEL
        ring
    · have hs : edgeSign k = 1 := by simp [edgeSign, h2]
      refine ⟨E, fun _ => edgeEL N a ε, fun j => ⟨?_, ?_⟩, fun B hB => ?_⟩
      · have h := hE j
        rw [hs, one_mul] at h
        linarith
      · have e : edgeEL N a ε - a = 2 * w := by unfold edgeEL; ring
        rw [e, abs_of_nonneg (by positivity)]
        linarith
      · funext j
        rw [hs, one_smul, one_mul]
  have e₁ : (fun ω => F (fun j => smCount (edgeSign k • QN Sig (X ω)) (etaE N ε) (E j)
      (edgeEL N (edgeSign k * a) ε))) = fun ω => smF F Sig (X ω) (etaE N ε) Ea Eb :=
    funext fun ω => by rw [hid _ (cmpQ_QN_isHermitian hSig _)]; rfl
  have e₀ : (fun ω => F (fun j => smCount (edgeSign k • QN Sig (gaussX M N ω)) (etaE N ε) (E j)
      (edgeEL N (edgeSign k * a) ε))) = fun ω => smF F Sig (gaussX M N ω) (etaE N ε) Ea Eb :=
    funext fun ω => by rw [hid _ (cmpQ_QN_isHermitian hSig _)]; rfl
  beta_reduce
  rw [e₁, e₀]
  -- the laws of `X`, `X⁰` and the function `Φ = F ∘ 𝒳 ∘ ofCoord`
  set ρ₀ : Fin M × Fin N → Measure ℝ := fun _ => gaussLaw N with hρ₀
  set ρ₁ : Fin M × Fin N → Measure ℝ := entryLaw X with hρ₁
  have : IsProbabilityMeasure (gaussLaw N) := cmpQ_gaussLaw_prob N
  have : ∀ α, IsProbabilityMeasure (ρ₀ α) := fun _ => cmpQ_gaussLaw_prob N
  have : ∀ α, IsProbabilityMeasure (ρ₁ α) := cmpQ_entryLaw_prob hX.entries
  set Φ : (Fin M × Fin N → ℝ) → ℝ := fun x => smF F Sig (ofCoord x) (etaE N ε) Ea Eb with hΦ
  have hΦc : Continuous Φ := hF.continuous.comp (continuous_pi fun j =>
    (cmpQ_continuous_smCount hSig hη (Ea j) (Eb j)).comp cmpQ_continuous_ofCoord)
  have hΦm : Measurable Φ := hΦc.measurable
  have hΦi : ∀ (ν : Measure (Fin M × Fin N → ℝ)) [IsFiniteMeasure ν], Integrable Φ ν :=
    fun ν _ => Integrable.of_bound hΦm.aestronglyMeasurable Cb
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFB _)
  have hvert : ∀ u, Integrable Φ (vertexLaw ρ₀ ρ₁ u) := fun u => by
    have : ∀ α, IsProbabilityMeasure (if u α then ρ₁ α else ρ₀ α) := fun α => by
      split <;> infer_instance
    have : IsProbabilityMeasure (vertexLaw ρ₀ ρ₁ u) := by unfold vertexLaw; infer_instance
    exact hΦi _
  have hX1 : ∫ ω, smF F Sig (X ω) (etaE N ε) Ea Eb = ∫ x, Φ x ∂(Measure.pi ρ₁) := by
    have hmeasX : ∀ β : Fin M × Fin N, Measurable fun ω => X ω β.1 β.2 :=
      fun β => hX.entries.measurable β.1 β.2
    have hg1 : Measurable fun ω (β : Fin M × Fin N) => X ω β.1 β.2 := measurable_pi_iff.2 hmeasX
    have hlaw : Measure.pi ρ₁ = (ℙ : Measure Ω).map (fun ω (β : Fin M × Fin N) => X ω β.1 β.2) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun β => (hmeasX β).aemeasurable)).1 hX.entries.indep]
      rfl
    rw [hlaw, integral_map hg1.aemeasurable hΦm.aestronglyMeasurable]
    rfl
  have hX0 : ∫ ω, smF F Sig (gaussX M N ω) (etaE N ε) Ea Eb = ∫ x, Φ x ∂(Measure.pi ρ₀) := rfl
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
    set T : Fin M × Fin N → ℝ := fun α => ∫ x, smT 3 F Sig (ofCoord x) (etaE N ε) Ea Eb α.1 α.2
      (ofCoord x α.1 α.2) ∂(interpLaw θ ρ₀ ρ₁) with hTdef
    have h3 : |∑ i, ∑ μ, m3 i μ * T (i, μ)| ≤ KT * S * Cb * (N : ℝ) ^ (4 / 3 + 21 * ε) :=
      hT N hNT (Ω := InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) M Sig ofCoord k m3 S F Cb Ea Eb
        hmodθ hk (fun i μ => cmpQ_abs_third_le hX.entries hN1 i μ) hF hFb hW
    have hG : EntryAssumption (momMax C) (gaussX M N) :=
      ((gaussX_isGaussianEnsemble M N).entryAssumption hN1).mono fun q => le_max_right _ _
    -- one entry: the swap of `y₁ ∼ law(X_α)` against `y₀ ∼ N(0, 1/N)` in `X^θ`
    have hent : ∀ α : Fin M × Fin N, |((∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α))) -
        ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) - m3 α.1 α.2 / 6 * T α| ≤
          KS * Cb * (N : ℝ) ^ (-7 / 3 + 20 * ε) := by
      intro α
      have : IsProbabilityMeasure (ρ₁ α) := cmpQ_entryLaw_prob hX.entries α
      have : IsProbabilityMeasure (ρ₀ α) := cmpQ_gaussLaw_prob N
      have : IsProbabilityMeasure
          (ℙ : Measure (CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α))) := cmpQ_prob _ _ _
      have hfm : Measurable fun ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          (ω.1 : InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) := measurable_fst
      have hE' := cmpQ_entry_transfer (Ω := InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁) hfm
        (by exact cmpQ_map_fst (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) hEθ
      have hmod' : IsModel τ (momMax C) M N Sig
          (fun ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
            ofCoord (ω.1 : InterpSpace (Fin M × Fin N) θ ρ₀ ρ₁)) :=
        ⟨hX.ratio_ge, hX.ratio_le, hE', hX.sigma⟩
      have hind := cmpQ_indep_fst_snd (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)
      have hind1 : IndepFun (fun ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          ofCoord (ω.1 : Fin M × Fin N → ℝ)) (fun ω => (ω.2.1 : ℝ)) :=
        hind.comp cmpQ_continuous_ofCoord.measurable measurable_fst
      have hind0 : IndepFun (fun ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          ofCoord (ω.1 : Fin M × Fin N → ℝ)) (fun ω => (ω.2.2 : ℝ)) :=
        hind.comp cmpQ_continuous_ofCoord.measurable measurable_snd
      have hlawG : ρ₀ α = entryLaw (gaussX M N) α :=
        ((gaussX_isGaussianEnsemble M N).law α.1 α.2).symm
      obtain ⟨m1, v1, p1⟩ := cmpQ_law_props (hX.entries.mono fun q => le_max_left (C q) _) α
      obtain ⟨m0, v0, p0⟩ := cmpQ_law_props hG α
      rw [← hlawG] at m0 v0 p0
      have hmean1 : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) = 0 :=
        (cmpQ_integral_y₁ _ _ _ (fun t => t)).trans m1
      have hmean0 : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) = 0 :=
        (cmpQ_integral_y₀ _ _ _ (fun t => t)).trans m0
      have hvar1 : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) ^ 2 =
          1 / (N : ℝ) := (cmpQ_integral_y₁ _ _ _ (fun t => t ^ 2)).trans v1
      have hvar0 : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) ^ 2 =
          1 / (N : ℝ) := (cmpQ_integral_y₀ _ _ _ (fun t => t ^ 2)).trans v0
      have hmom1 : ∀ p : ℕ, Integrable (fun ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          |Real.sqrt N * (ω.2.1 : ℝ)| ^ p) ∧
          ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), |Real.sqrt N * (ω.2.1 : ℝ)| ^ p ≤
            momMax C p := fun p =>
        ⟨cmpQ_integrable_y₁ _ _ _ (p1 p).1,
          (cmpQ_integral_y₁ _ _ _ (fun t => |Real.sqrt N * t| ^ p)).trans_le (p1 p).2⟩
      have hmom0 : ∀ p : ℕ, Integrable (fun ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) =>
          |Real.sqrt N * (ω.2.2 : ℝ)| ^ p) ∧
          ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), |Real.sqrt N * (ω.2.2 : ℝ)| ^ p ≤
            momMax C p := fun p =>
        ⟨cmpQ_integrable_y₀ _ _ _ (p0 p).1,
          (cmpQ_integral_y₀ _ _ _ (fun t => |Real.sqrt N * t| ^ p)).trans_le (p0 p).2⟩
      have hsw := hS N hNS (Ω := CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α)) M Sig
        (fun ω => ofCoord (ω.1 : Fin M × Fin N → ℝ)) k (fun ω => (ω.2.1 : ℝ))
        (fun ω => (ω.2.2 : ℝ)) α.1 α.2 F Cb Ea Eb hmod' hk hind1 hind0
        (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd) hmean1 hmean0
        hvar1 hvar0 hmom1 hmom0 hF hFb hW
      have e1 : ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α)) =
          ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smF F Sig (Xupd (ofCoord (ω.1 : Fin M × Fin N → ℝ)) α.1 α.2 (ω.2.1 : ℝ))
              (etaE N ε) Ea Eb := by
        have := hAt (ρ₁ α) α
        rw [integral_interpLawAt_eq α (ρ₁ α) hΦm (hΦi _), ← cmpQ_integral_pair₁
          (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) (g := fun q => Φ (Function.update q.1 α q.2))
          (hΦm.comp measurable_update')]
        simp only [hΦ, cmpQ_ofCoord_update]
      have e0 : ∫ x, Φ x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)) =
          ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
            smF F Sig (Xupd (ofCoord (ω.1 : Fin M × Fin N → ℝ)) α.1 α.2 (ω.2.2 : ℝ))
              (etaE N ε) Ea Eb := by
        have := hAt (ρ₀ α) α
        rw [integral_interpLawAt_eq α (ρ₀ α) hΦm (hΦi _), ← cmpQ_integral_pair₀
          (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α) (g := fun q => Φ (Function.update q.1 α q.2))
          (hΦm.comp measurable_update')]
        simp only [hΦ, cmpQ_ofCoord_update]
      have a1 : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) ^ 3 =
          ∫ t, t ^ 3 ∂(ρ₁ α) := cmpQ_integral_y₁ _ _ _ (fun t => t ^ 3)
      have a1' : ∫ t, t ^ 3 ∂(ρ₁ α) = m3 α.1 α.2 :=
        cmpQ_integral_entryLaw hX.entries α (f := fun t => t ^ 3) (by fun_prop)
      have a0 : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) ^ 3 =
          ∫ t, t ^ 3 ∂(ρ₀ α) := cmpQ_integral_y₀ _ _ _ (fun t => t ^ 3)
      have a0' : ∫ t, t ^ 3 ∂(ρ₀ α) = 0 := by
        rw [hlawG]
        exact (cmpQ_integral_entryLaw hG α (f := fun t => t ^ 3) (by fun_prop)).trans
          (zeroThird_gaussX M N α.1 α.2)
      have c1 : (∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.1 : ℝ) ^ 3) -
          (∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α), (ω.2.2 : ℝ) ^ 3) =
            m3 α.1 α.2 := by
        rw [a1, a1', a0, a0', sub_zero]
      have tT : ∫ ω : CmpSpace M N (interpLaw θ ρ₀ ρ₁) (ρ₁ α) (ρ₀ α),
          smT 3 F Sig (ofCoord (ω.1 : Fin M × Fin N → ℝ)) (etaE N ε) Ea Eb α.1 α.2
            (ofCoord (ω.1 : Fin M × Fin N → ℝ) α.1 α.2) = T α :=
        cmpQ_integral_fst _ _ _
          (fun x => smT 3 F Sig (ofCoord x) (etaE N ε) Ea Eb α.1 α.2 (ofCoord x α.1 α.2))
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
  exact cmpQ_final hN1 hε hτ hM (le_max_right KS 0) hCb
    (cmpQ_le_rpow hA0 (by positivity) hNA)


/-- The comparison hypothesis at the Marchenko–Pastur point, Rademacher against Gaussian entries,
with every hypothesis of `smoothComparable_Q` discharged. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    SmoothComparable (2 * n) (edgeSign 1 * edgeVal (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1)
      (1 / 200) (1 / 6 - 25 * (1 / 200)) 1
      (fun ω => edgeSign 1 • QN (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω))
      (fun ω => edgeSign 1 • QN (1 : Matrix (Fin n) (Fin n) ℝ) (gaussX n (2 * n) ω)) := by
  obtain ⟨N₀, h⟩ := smoothComparable_Q (1 / 5) (fun _ => 1) 1 (1 / 200) (by norm_num)
    (by norm_num) le_rfl
  refine ⟨N₀, fun n hn hN => ?_⟩
  have hk : RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
    rw [specOf_one_eq]; exact regularEdge_mp hn
  exact h (2 * n) hN n 1 (radXn n) 1 (isModel_radXn hn) hk

end Anisotropic
