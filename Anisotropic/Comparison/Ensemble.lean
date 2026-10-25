import Anisotropic.Comparison.Interpolation
import Anisotropic.Framework.Model
import Anisotropic.Probability.NormBound.GaussianLower
import Anisotropic.Gaussian.Ensemble

/-!
# Interpolated ensembles, moment function, model classes

Section 7: the ensembles `X^θ` of Definition 7.6 viewed as coordinate matrices on `InterpSpace`,
the entry laws, the Gaussian entry law `N(0, 1/N)`, the moment function `C'_p = max(C_p, E|g|^p)`
of the interpolating ensembles, and the model classes (`zeroThird`, `allModels`). The entry
conditions and the vanishing of third moments pass from `X` to `X^θ`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Interpolated ensembles, moment function, model classes -/

/-- The coordinate matrix `x ↦ (x (i, μ))_{iμ}`. -/
def ofCoord (x : Fin M × Fin N → ℝ) : Matrix (Fin M) (Fin N) ℝ := fun i μ => x (i, μ)

/-- The law of the entry `X_α`. -/
def entryLaw {Ω : Type*} [MeasureSpace Ω] (X : Ω → Matrix (Fin M) (Fin N) ℝ)
    (α : Fin M × Fin N) : Measure ℝ :=
  (ℙ : Measure Ω).map fun ω => X ω α.1 α.2

/-- The law `N(0, 1/N)` of the entries of `X⁰`. -/
def gaussLaw (N : ℕ) : Measure ℝ := gaussianReal 0 (N : ℝ≥0)⁻¹

/-- The moment function `C'_p = max(C_p, E|g|^p)` of the interpolating ensembles. -/
def momMax (C : ℕ → ℝ) (p : ℕ) : ℝ := max (C p) (gaussMoment p)

/-- A class of random matrices (a predicate on all probability spaces `Ω : Type`). -/
abbrev ModelClass (M N : ℕ) : Type 1 :=
  ∀ (Ω : Type) [MeasureSpace Ω], (Ω → Matrix (Fin M) (Fin N) ℝ) → Prop

/-- (zero_third_moment): `E X_{iμ}³ = 0` for all `i, μ`. -/
def zeroThird : ModelClass M N := fun _ _ X => ∀ i μ, ∫ ω, X ω i μ ^ 3 = 0

/-- The class of all random matrices (no condition beyond the entry assumptions). -/
def allModels : ModelClass M N := fun _ _ _ => True

/-! ## Laws of the entries -/

/-- The moment conditions of the entry assumptions, for a single law on `ℝ`. -/
private structure LawProps (N : ℕ) (C : ℕ → ℝ) (ν : Measure ℝ) : Prop where
  integrable : ∀ p : ℕ, Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν
  mean : ∫ x, x ∂ν = 0
  var : ∫ x, x ^ 2 ∂ν = 1 / (N : ℝ)
  moment : ∀ p : ℕ, ∫ x, |Real.sqrt N * x| ^ p ∂ν ≤ C p

private instance gaussLaw_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (gaussLaw N) := by
  unfold gaussLaw
  infer_instance

private lemma entryLaw_isProbabilityMeasure {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {K : ℕ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : ∀ i μ, Measurable fun ω => X ω i μ) (α : Fin K × Fin N) :
    IsProbabilityMeasure (entryLaw X α) :=
  ⟨by
    simp [entryLaw, Measure.map_apply (hX α.1 α.2) MeasurableSet.univ]⟩

private lemma entryLaw_props {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (hX : EntryAssumption C X) (i : Fin K) (μ : Fin N) :
    LawProps N C (entryLaw X (i, μ)) := by
  have hm : AEMeasurable (fun ω => X ω i μ) (ℙ : Measure Ω) := (hX.measurable i μ).aemeasurable
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∫ x, f x ∂(entryLaw X (i, μ)) = ∫ ω, f (X ω i μ) := fun f hf =>
    integral_map hm hf.aestronglyMeasurable
  refine ⟨fun p => ?_, ?_, ?_, fun p => ?_⟩
  · exact (integrable_map_measure
      (by fun_prop : Continuous fun x : ℝ => |Real.sqrt N * x| ^ p).aestronglyMeasurable
      hm).2 (hX.integrable_moment p i μ)
  · simpa using (key (fun x => x) continuous_id).trans (hX.mean i μ)
  · exact (key (fun x => x ^ 2) (by fun_prop)).trans (hX.var i μ)
  · exact (key (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le (hX.moment p i μ)

private lemma gaussLaw_props (hN : 1 ≤ N) : LawProps N gaussMoment (gaussLaw N) := by
  have h := entryLaw_props ((gaussX_isGaussianEnsemble 1 N).entryAssumption hN) 0 ⟨0, hN⟩
  have hl : entryLaw (gaussX 1 N) ((0 : Fin 1), (⟨0, hN⟩ : Fin N)) = gaussLaw N :=
    (gaussX_isGaussianEnsemble 1 N).law 0 ⟨0, hN⟩
  rwa [hl] at h

/-- Integrability of `|√N x|^p` gives integrability of `x^p`. -/
private lemma integrable_pow_of_sqrt (hN : 1 ≤ N) {ν : Measure ℝ} {p : ℕ}
    (h : Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν) :
    Integrable (fun x : ℝ => x ^ p) ν := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine (h.const_mul ((Real.sqrt N)⁻¹ ^ p)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hs.ne', one_pow, one_mul]

private lemma integrable_mixMeasure {θ : ℝ} {ρ₀ ρ₁ : Measure ℝ} {f : ℝ → ℝ}
    (hf₀ : Integrable f ρ₀) (hf₁ : Integrable f ρ₁) : Integrable f (mixMeasure θ ρ₀ ρ₁) :=
  (hf₁.smul_measure ENNReal.ofReal_ne_top).add_measure (hf₀.smul_measure ENNReal.ofReal_ne_top)

private lemma mix_props (hN : 1 ≤ N) {C₀ C₁ : ℕ → ℝ} {ν₀ ν₁ : Measure ℝ} (h₀ : LawProps N C₀ ν₀)
    (h₁ : LawProps N C₁ ν₁) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    LawProps N (fun p => max (C₁ p) (C₀ p)) (mixMeasure θ ν₀ ν₁) := by
  have hi : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ p) ν₀ ∧ Integrable (fun x : ℝ => x ^ p) ν₁ :=
    fun p => ⟨integrable_pow_of_sqrt hN (h₀.integrable p),
      integrable_pow_of_sqrt hN (h₁.integrable p)⟩
  refine ⟨fun p => integrable_mixMeasure (h₀.integrable p) (h₁.integrable p), ?_, ?_, fun p => ?_⟩
  · have e := integral_mixMeasure hθ₀ hθ₁ (by simpa using (hi 1).1) (by simpa using (hi 1).2)
    rw [e, h₀.mean, h₁.mean]
    ring
  · rw [integral_mixMeasure hθ₀ hθ₁ (hi 2).1 (hi 2).2, h₀.var, h₁.var]
    ring
  · rw [integral_mixMeasure hθ₀ hθ₁ (h₀.integrable p) (h₁.integrable p)]
    have a := (h₁.moment p).trans (le_max_left (C₁ p) (C₀ p))
    have b := (h₀.moment p).trans (le_max_right (C₁ p) (C₀ p))
    have := mul_le_mul_of_nonneg_left a hθ₀
    have := mul_le_mul_of_nonneg_left b (sub_nonneg.2 hθ₁)
    nlinarith

/-- Coordinate integrals under `∏_α ρ^θ_α` are integrals against the coordinate law. -/
private lemma integral_interp_coord {ι : Type} [Fintype ι] (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : ι) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (mixMeasure θ (ρ₀ α) (ρ₁ α))) :
    ∫ ω, f (ω α) ∂(interpLaw θ ρ₀ ρ₁) = ∫ x, f x ∂(mixMeasure θ (ρ₀ α) (ρ₁ α)) := by
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  exact integral_comp_eval (μ := fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) hf

private lemma integrable_interp_coord {ι : Type} [Fintype ι] (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ)
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : ι) {f : ℝ → ℝ}
    (hf : Integrable f (mixMeasure θ (ρ₀ α) (ρ₁ α))) :
    Integrable (fun ω => f (ω α)) (interpLaw θ ρ₀ ρ₁) := by
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) :=
    fun β => isProbabilityMeasure_mixMeasure θ _ _
  exact integrable_comp_eval (μ := fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) hf

private lemma integral_cube_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  have h := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ => -x) (f := fun x : ℝ => x ^ 3)
    (by fun_prop) (by fun_prop)
  rw [gaussianReal_map_neg, neg_zero] at h
  have e : ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) := fun x => by ring
  simp_rw [e, integral_neg] at h
  linarith

theorem EntryAssumption.mono {Ω : Type*} [MeasureSpace Ω] {C C' : ℕ → ℝ} {K : ℕ}
    {X : Ω → Matrix (Fin K) (Fin N) ℝ} (h : EntryAssumption C X) (hC : ∀ p, C p ≤ C' p) :
    EntryAssumption C' X :=
  ⟨h.measurable, h.indep, h.mean, h.var, h.integrable_moment, fun p i μ => (h.moment p i μ).trans (hC p)⟩

/-- `X^θ` satisfies (cond on entries of X), (moments of X-1) with `C' = momMax C`. -/
theorem entryAssumption_interp {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (hN : 1 ≤ N)
    {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    EntryAssumption (momMax C)
      (Ω := InterpSpace (Fin M × Fin N) θ (fun _ => gaussLaw N) (entryLaw X)) ofCoord := by
  have : ∀ α, IsProbabilityMeasure (entryLaw X α) :=
    entryLaw_isProbabilityMeasure hX.measurable
  have : ∀ α : Fin M × Fin N, IsProbabilityMeasure ((fun _ => gaussLaw N) α) :=
    fun _ => inferInstance
  have hP : ∀ α : Fin M × Fin N,
      LawProps N (momMax C) (mixMeasure θ (gaussLaw N) (entryLaw X α)) := fun α =>
    mix_props hN (gaussLaw_props hN) (entryLaw_props hX α.1 α.2) h₀ h₁
  have key : ∀ (i : Fin M) (μ : Fin N) (f : ℝ → ℝ), Continuous f →
      ∫ ω, f (ofCoord ω i μ) ∂(interpLaw θ (fun _ => gaussLaw N) (entryLaw X)) =
        ∫ x, f x ∂(mixMeasure θ (gaussLaw N) (entryLaw X (i, μ))) := fun i μ f hf =>
    integral_interp_coord θ (fun _ => gaussLaw N) (entryLaw X) (i, μ) hf.aestronglyMeasurable
  have hmix : ∀ α : Fin M × Fin N,
      IsProbabilityMeasure (mixMeasure θ (gaussLaw N) (entryLaw X α)) :=
    fun α => isProbabilityMeasure_mixMeasure θ _ _
  refine ⟨fun i μ => measurable_pi_apply (X := fun _ : Fin M × Fin N => ℝ) (i, μ), ?_, ?_, ?_,
    ?_, ?_⟩
  · exact iIndepFun_pi
      (μ := fun α : Fin M × Fin N => mixMeasure θ (gaussLaw N) (entryLaw X α))
      (X := fun _ x => x) fun _ => aemeasurable_id
  · intro i μ
    exact (key i μ (fun x => x) continuous_id).trans (hP (i, μ)).mean
  · intro i μ
    exact (key i μ (fun x => x ^ 2) (by fun_prop)).trans (hP (i, μ)).var
  · intro p i μ
    exact integrable_interp_coord θ (fun _ => gaussLaw N) (entryLaw X) (i, μ)
      (f := fun x : ℝ => |Real.sqrt N * x| ^ p) ((hP (i, μ)).integrable p)
  · intro p i μ
    exact (key i μ (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le
      ((hP (i, μ)).moment p)

/-- The Gaussian ensemble has vanishing third moments. -/
theorem zeroThird_gaussX (M N : ℕ) : zeroThird (GaussSpace M N) (gaussX M N) := by
  intro i μ
  have hm : AEMeasurable (fun ω => gaussX M N ω i μ) (ℙ : Measure (GaussSpace M N)) :=
    ((gaussX_isGaussianEnsemble M N).measurable i μ).aemeasurable
  have h := integral_map (μ := (ℙ : Measure (GaussSpace M N))) (f := fun x : ℝ => x ^ 3) hm
    (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable
  rw [(gaussX_isGaussianEnsemble M N).law i μ, integral_cube_gaussianReal] at h
  exact h.symm

/-- `zeroThird_gaussX` at `M = N = 2`. -/
example : zeroThird (GaussSpace 2 2) (gaussX 2 2) := zeroThird_gaussX 2 2

end Anisotropic

#print axioms Anisotropic.EntryAssumption.mono
#print axioms Anisotropic.entryAssumption_interp
#print axioms Anisotropic.zeroThird_gaussX
