import Mathlib

/-!
# Bernoulli interpolation at the level of laws

Section 7: the interpolating laws `ρ^θ = θ ρ¹ + (1 − θ) ρ⁰` of Definition 7.6, the law of `X^θ`
and of `X^{θ,y}_{(α)}`, the expansion of `E F(X^θ)` as a multi-affine polynomial in `θ` over the
vertices `u ∈ {0,1}^ι`, its derivative (Remark 7.18), and the interpolation formula (interpol)
of Lemma 7.9. The random matrices of Definition 7.6 are represented by their laws: `X^θ` lives
on `InterpSpace`, and the pair `(X^θ, y)` with `y` independent of `X^θ` lives on `PairSpace`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Bernoulli interpolation at the level of laws (Definition 7.6, Lemma 7.9, Remark 7.18) -/

section Interpolation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The interpolation weight `θ` clamped to `[0, 1]`. -/
def unitClamp (θ : ℝ) : ℝ := max 0 (min θ 1)

/-- Definition 7.6: the law `ρ^θ = θ ρ¹ + (1 − θ) ρ⁰` (weight clamped to `[0, 1]`). -/
def mixMeasure (θ : ℝ) (ρ₀ ρ₁ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (unitClamp θ) • ρ₁ + ENNReal.ofReal (1 - unitClamp θ) • ρ₀

/-- Definition 7.6: the law `∏_α ρ^θ_α` of `X^θ`. -/
def interpLaw (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ) : Measure (ι → ℝ) :=
  Measure.pi fun α => mixMeasure θ (ρ₀ α) (ρ₁ α)

/-- The law of `X^{θ, X^u_α}_{(α)}`: the factor `α` of `∏_β ρ^θ_β` replaced by `ρ`. -/
def interpLawAt (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ) (α : ι) (ρ : Measure ℝ) : Measure (ι → ℝ) :=
  Measure.pi (Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ)

/-- The vertex law `∏_α ρ^{u_α}_α`, `u ∈ {0,1}^ι`. -/
def vertexLaw (ρ₀ ρ₁ : ι → Measure ℝ) (u : ι → Bool) : Measure (ι → ℝ) :=
  Measure.pi fun α => if u α then ρ₁ α else ρ₀ α

/-- The multi-affine polynomial `θ ↦ ∑_u ∏_α θ^{u_α} (1 − θ)^{1 − u_α} E_u F`, equal to
`E F(X^θ)` on `[0, 1]`. -/
def interpPoly (ρ₀ ρ₁ : ι → Measure ℝ) (F : (ι → ℝ) → ℝ) (θ : ℝ) : ℝ :=
  ∑ u : ι → Bool, (∏ α, if u α then θ else 1 - θ) * ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u)

private lemma unitClamp_nonneg (θ : ℝ) : 0 ≤ unitClamp θ := le_max_left _ _

private lemma unitClamp_le_one (θ : ℝ) : unitClamp θ ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

private lemma unitClamp_of_mem {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) : unitClamp θ = θ := by
  unfold unitClamp
  rw [min_eq_left h₁, max_eq_right h₀]

theorem isProbabilityMeasure_mixMeasure (θ : ℝ) (ρ₀ ρ₁ : Measure ℝ) [IsProbabilityMeasure ρ₀]
    [IsProbabilityMeasure ρ₁] : IsProbabilityMeasure (mixMeasure θ ρ₀ ρ₁) := by
  constructor
  simp only [mixMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (unitClamp_nonneg θ) (sub_nonneg.2 (unitClamp_le_one θ))]
  simp

theorem integral_mixMeasure {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) {ρ₀ ρ₁ : Measure ℝ}
    {f : ℝ → ℝ} (hf₀ : Integrable f ρ₀) (hf₁ : Integrable f ρ₁) :
    ∫ x, f x ∂(mixMeasure θ ρ₀ ρ₁) = θ * ∫ x, f x ∂ρ₁ + (1 - θ) * ∫ x, f x ∂ρ₀ := by
  have hi₁ : Integrable f (ENNReal.ofReal (unitClamp θ) • ρ₁) :=
    hf₁.smul_measure ENNReal.ofReal_ne_top
  have hi₀ : Integrable f (ENNReal.ofReal (1 - unitClamp θ) • ρ₀) :=
    hf₀.smul_measure ENNReal.ofReal_ne_top
  rw [mixMeasure, integral_add_measure hi₁ hi₀, integral_smul_measure, integral_smul_measure,
    unitClamp_of_mem h₀ h₁, ENNReal.toReal_ofReal h₀, ENNReal.toReal_ofReal (sub_nonneg.2 h₁),
    smul_eq_mul, smul_eq_mul]

/-- Multilinear expansion of a product of two-term mixtures over the vertices `u ∈ {0,1}^ι`. -/
private lemma pi_mix_expand (p q : ι → ℝ) (hp : ∀ α, 0 ≤ p α) (hq : ∀ α, 0 ≤ q α)
    (ρ₀ ρ₁ : ι → Measure ℝ) [∀ α, IsProbabilityMeasure (ρ₀ α)]
    [∀ α, IsProbabilityMeasure (ρ₁ α)] :
    Measure.pi (fun α => ENNReal.ofReal (p α) • ρ₁ α + ENNReal.ofReal (q α) • ρ₀ α) =
      ∑ u : ι → Bool, ENNReal.ofReal (∏ α, if u α then p α else q α) • vertexLaw ρ₀ ρ₁ u := by
  have : ∀ α, IsFiniteMeasure (ENNReal.ofReal (p α) • ρ₁ α + ENNReal.ofReal (q α) • ρ₀ α) :=
    fun α => ⟨by
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩⟩
  have : ∀ (u : ι → Bool) α, IsProbabilityMeasure (if u α then ρ₁ α else ρ₀ α) :=
    fun u α => by split <;> infer_instance
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.finsetSum_apply]
  have key : ∀ u : ι → Bool,
      (ENNReal.ofReal (∏ α, if u α then p α else q α) • vertexLaw ρ₀ ρ₁ u) (Set.univ.pi s) =
        ∏ α, (if u α then ENNReal.ofReal (p α) * ρ₁ α (s α)
          else ENNReal.ofReal (q α) * ρ₀ α (s α)) := by
    intro u
    rw [Measure.smul_apply, vertexLaw, Measure.pi_pi, smul_eq_mul,
      ENNReal.ofReal_prod_of_nonneg (fun α _ => by by_cases h : u α <;> simp [h, hp, hq]),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun α _ => ?_
    by_cases h : u α <;> simp [h]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun α (b : Bool) => if b then ENNReal.ofReal (p α) * ρ₁ α (s α)
    else ENNReal.ofReal (q α) * ρ₀ α (s α))]
  refine Finset.prod_congr rfl fun α _ => ?_
  simp

/-- Integral form of the multilinear expansion, given integrability at every vertex. -/
private lemma integral_pi_mix (p q : ι → ℝ) (hp : ∀ α, 0 ≤ p α) (hq : ∀ α, 0 ≤ q α)
    (ρ₀ ρ₁ : ι → Measure ℝ) [∀ α, IsProbabilityMeasure (ρ₀ α)]
    [∀ α, IsProbabilityMeasure (ρ₁ α)] {F : (ι → ℝ) → ℝ}
    (hint : ∀ u, Integrable F (vertexLaw ρ₀ ρ₁ u)) :
    ∫ x, F x ∂(Measure.pi fun α => ENNReal.ofReal (p α) • ρ₁ α + ENNReal.ofReal (q α) • ρ₀ α) =
      ∑ u : ι → Bool, (∏ α, if u α then p α else q α) * ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u) := by
  rw [pi_mix_expand p q hp hq,
    integral_finsetSum_measure fun u _ => (hint u).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal
    (Finset.prod_nonneg fun α _ => by by_cases h : u α <;> simp [h, hp, hq]), smul_eq_mul]

/-- On `[0, 1]`, `interpLawAt θ ρ₀ ρ₁ α (a ρ¹_α + b ρ⁰_α)` is a product of two-term mixtures. -/
private lemma interpLawAt_mix_eq {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) (ρ₀ ρ₁ : ι → Measure ℝ)
    (α : ι) (a b : ℝ) :
    interpLawAt θ ρ₀ ρ₁ α (ENNReal.ofReal a • ρ₁ α + ENNReal.ofReal b • ρ₀ α) =
      Measure.pi fun β => ENNReal.ofReal (Function.update (fun _ => θ) α a β) • ρ₁ β +
        ENNReal.ofReal (Function.update (fun _ => 1 - θ) α b β) • ρ₀ β := by
  unfold interpLawAt
  congr 1
  funext β
  by_cases h : β = α
  · subst h
    simp
  · simp [Function.update_of_ne h, mixMeasure, unitClamp_of_mem h₀ h₁]

private lemma prod_update_ite (u : ι → Bool) (α : ι) (θ a b : ℝ) :
    (∏ β, if u β then Function.update (fun _ => θ) α a β
      else Function.update (fun _ => 1 - θ) α b β) =
      (if u α then a else b) * ∏ β ∈ Finset.univ.erase α, if u β then θ else 1 - θ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ α)]
  congr 1
  · by_cases h : u α <;> simp [h]
  · refine Finset.prod_congr rfl fun β hβ => ?_
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hβ)]

/-- `E F(X^{θ,y}_{(α)})` for `y ∼ a ρ¹_α + b ρ⁰_α`, expanded over the vertices. -/
private lemma integral_interpLawAt_mix {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1)
    {ρ₀ ρ₁ : ι → Measure ℝ} [∀ α, IsProbabilityMeasure (ρ₀ α)]
    [∀ α, IsProbabilityMeasure (ρ₁ α)] {F : (ι → ℝ) → ℝ}
    (hint : ∀ u, Integrable F (vertexLaw ρ₀ ρ₁ u)) (α : ι) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ENNReal.ofReal a • ρ₁ α + ENNReal.ofReal b • ρ₀ α)) =
      ∑ u : ι → Bool, ((if u α then a else b) *
        ∏ β ∈ Finset.univ.erase α, if u β then θ else 1 - θ) * ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u) := by
  have hp : ∀ β, 0 ≤ Function.update (fun _ => θ) α a β := fun β => by
    by_cases h : β = α
    · subst h; simpa using ha
    · simpa [Function.update_of_ne h] using h₀
  have hq : ∀ β, 0 ≤ Function.update (fun _ => 1 - θ) α b β := fun β => by
    by_cases h : β = α
    · subst h; simpa using hb
    · simpa [Function.update_of_ne h] using h₁
  rw [interpLawAt_mix_eq h₀ h₁, integral_pi_mix _ _ hp hq ρ₀ ρ₁ hint]
  simp_rw [prod_update_ite]

private lemma mix_one_zero (μ ν : Measure ℝ) :
    ENNReal.ofReal 1 • μ + ENNReal.ofReal 0 • ν = μ := by simp

private lemma mix_zero_one (μ ν : Measure ℝ) :
    ENNReal.ofReal 0 • μ + ENNReal.ofReal 1 • ν = ν := by simp

/-- `E F(X^θ)` is the multi-affine polynomial on `[0, 1]`, given integrability at every vertex. -/
theorem integral_interpLaw_eq_interpPoly {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1)
    {ρ₀ ρ₁ : ι → Measure ℝ} [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)]
    {F : (ι → ℝ) → ℝ} (hF : Measurable F) (hint : ∀ u, Integrable F (vertexLaw ρ₀ ρ₁ u)) :
    ∫ x, F x ∂(interpLaw θ ρ₀ ρ₁) = interpPoly ρ₀ ρ₁ F θ := by
  have hlaw : interpLaw θ ρ₀ ρ₁ =
      Measure.pi fun α => ENNReal.ofReal ((fun _ : ι => θ) α) • ρ₁ α +
        ENNReal.ofReal ((fun _ : ι => 1 - θ) α) • ρ₀ α := by
    unfold interpLaw
    congr 1
    funext α
    simp [mixMeasure, unitClamp_of_mem h₀ h₁]
  rw [hlaw, integral_pi_mix _ _ (fun _ => h₀) (fun _ => sub_nonneg.2 h₁) ρ₀ ρ₁ hint]
  rfl

private lemma continuous_ite_affine (b : Bool) :
    Continuous fun t : ℝ => if b then t else 1 - t := by
  cases b
  · exact continuous_const.sub continuous_id
  · exact continuous_id

/-- The derivative of the polynomial `interpPoly` at every real `θ`. -/
private lemma hasDerivAt_interpPoly_expand (ρ₀ ρ₁ : ι → Measure ℝ) (F : (ι → ℝ) → ℝ) (θ : ℝ) :
    HasDerivAt (interpPoly ρ₀ ρ₁ F)
      (∑ u : ι → Bool, (∑ α, (∏ β ∈ Finset.univ.erase α, if u β then θ else 1 - θ) *
        (if u α then 1 else -1)) * ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u)) θ := by
  have hfun : interpPoly ρ₀ ρ₁ F = fun t => ∑ u : ι → Bool,
      (∏ α, if u α then t else 1 - t) * ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u) := rfl
  rw [hfun]
  refine HasDerivAt.fun_sum fun u _ => HasDerivAt.mul_const ?_ _
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := θ)
    (f := fun α t => if u α then t else 1 - t) (f' := fun α => if u α then 1 else -1)
    fun α _ => by
      by_cases h : u α
      · simpa [h] using hasDerivAt_id' θ
      · simpa [h] using (hasDerivAt_id' θ).const_sub 1
  simpa [smul_eq_mul] using h

private lemma continuous_interpPoly_deriv (ρ₀ ρ₁ : ι → Measure ℝ) (F : (ι → ℝ) → ℝ) :
    Continuous fun θ : ℝ => ∑ u : ι → Bool, (∑ α, (∏ β ∈ Finset.univ.erase α,
      if u β then θ else 1 - θ) * (if u α then 1 else -1)) * ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u) :=
  continuous_finsetSum _ fun _ _ => (continuous_finsetSum _ fun _ _ =>
    (continuous_finsetProd _ fun _ _ => continuous_ite_affine _).mul continuous_const).mul
      continuous_const

/-- Remark 7.18: `d/dθ E F(X^θ) = ∑_α [E F(X^{θ,X¹_α}_{(α)}) − E F(X^{θ,X⁰_α}_{(α)})]`. -/
theorem hasDerivAt_interpPoly {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1)
    {ρ₀ ρ₁ : ι → Measure ℝ} [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)]
    {F : (ι → ℝ) → ℝ} (hF : Measurable F) (hint : ∀ u, Integrable F (vertexLaw ρ₀ ρ₁ u)) :
    HasDerivAt (interpPoly ρ₀ ρ₁ F)
      (∑ α, (∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α)) - ∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))))
      θ := by
  refine (hasDerivAt_interpPoly_expand ρ₀ ρ₁ F θ).congr_deriv ?_
  have hI₁ : ∀ α, ∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α)) = ∑ u : ι → Bool,
      ((if u α then 1 else 0) * ∏ β ∈ Finset.univ.erase α, if u β then θ else 1 - θ) *
        ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u) := fun α => by
    rw [← integral_interpLawAt_mix h₀ h₁ hint α zero_le_one le_rfl, mix_one_zero]
  have hI₀ : ∀ α, ∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α)) = ∑ u : ι → Bool,
      ((if u α then 0 else 1) * ∏ β ∈ Finset.univ.erase α, if u β then θ else 1 - θ) *
        ∫ x, F x ∂(vertexLaw ρ₀ ρ₁ u) := fun α => by
    rw [← integral_interpLawAt_mix h₀ h₁ hint α le_rfl zero_le_one, mix_zero_one]
  simp_rw [hI₁, hI₀, ← Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun u _ => ?_
  by_cases h : u α <;> simp [h]

omit [DecidableEq ι] in
private lemma interpLaw_one (ρ₀ ρ₁ : ι → Measure ℝ) : interpLaw 1 ρ₀ ρ₁ = Measure.pi ρ₁ := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

omit [DecidableEq ι] in
private lemma interpLaw_zero (ρ₀ ρ₁ : ι → Measure ℝ) : interpLaw 0 ρ₀ ρ₁ = Measure.pi ρ₀ := by
  unfold interpLaw
  congr 1
  funext α
  simp [mixMeasure, unitClamp]

/-- Lemma 7.9 (interpol), with the integrability hypotheses made explicit. -/
theorem interpol {ρ₀ ρ₁ : ι → Measure ℝ} [∀ α, IsProbabilityMeasure (ρ₀ α)]
    [∀ α, IsProbabilityMeasure (ρ₁ α)] {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    (hint : ∀ u, Integrable F (vertexLaw ρ₀ ρ₁ u)) :
    ∫ x, F x ∂(Measure.pi ρ₁) - ∫ x, F x ∂(Measure.pi ρ₀) =
      ∫ θ in (0 : ℝ)..1, ∑ α,
        (∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₁ α)) - ∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α (ρ₀ α))) := by
  have hD : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (interpPoly ρ₀ ρ₁ F)
      (∑ α, (∫ y, F y ∂(interpLawAt x ρ₀ ρ₁ α (ρ₁ α)) -
        ∫ y, F y ∂(interpLawAt x ρ₀ ρ₁ α (ρ₀ α)))) x := fun x hx => by
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact hasDerivAt_interpPoly hx.1 hx.2 hF hint
  have hcont : ContinuousOn (fun x : ℝ => ∑ α, (∫ y, F y ∂(interpLawAt x ρ₀ ρ₁ α (ρ₁ α)) -
      ∫ y, F y ∂(interpLawAt x ρ₀ ρ₁ α (ρ₀ α)))) (Set.uIcc 0 1) :=
    (continuous_interpPoly_deriv ρ₀ ρ₁ F).continuousOn.congr fun x hx =>
      (hD x hx).unique (hasDerivAt_interpPoly_expand ρ₀ ρ₁ F x)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable,
    ← integral_interpLaw_eq_interpPoly zero_le_one le_rfl hF hint,
    ← integral_interpLaw_eq_interpPoly le_rfl zero_le_one hF hint, interpLaw_one, interpLaw_zero]

/-- `E F(X^{θ,y}_{(α)})` for `y ∼ ρ` independent of `X^θ`: the law `interpLawAt`. -/
theorem integral_interpLawAt_eq {θ : ℝ} {ρ₀ ρ₁ : ι → Measure ℝ}
    [∀ α, IsProbabilityMeasure (ρ₀ α)] [∀ α, IsProbabilityMeasure (ρ₁ α)] (α : ι)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    (hint : Integrable F (interpLawAt θ ρ₀ ρ₁ α ρ)) :
    ∫ x, F x ∂(interpLawAt θ ρ₀ ρ₁ α ρ) =
      ∫ q, F (Function.update q.1 α q.2) ∂((interpLaw θ ρ₀ ρ₁).prod ρ) := by
  have : ∀ β, IsProbabilityMeasure (mixMeasure θ (ρ₀ β) (ρ₁ β)) := fun β =>
    isProbabilityMeasure_mixMeasure _ _ _
  have : ∀ β, IsProbabilityMeasure
      (Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ β) := fun β => by
    by_cases h : β = α
    · subst h; simpa using ‹IsProbabilityMeasure ρ›
    · simpa [Function.update_of_ne h] using isProbabilityMeasure_mixMeasure θ (ρ₀ β) (ρ₁ β)
  have hφ : Measurable fun q : (ι → ℝ) × ℝ => Function.update q.1 α q.2 := measurable_update'
  have hmap : ((interpLaw θ ρ₀ ρ₁).prod ρ).map
      (fun q : (ι → ℝ) × ℝ => Function.update q.1 α q.2) = interpLawAt θ ρ₀ ρ₁ α ρ := by
    unfold interpLawAt
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hφ (MeasurableSet.univ_pi hs)]
    have hpre : (fun q : (ι → ℝ) × ℝ => Function.update q.1 α q.2) ⁻¹' Set.univ.pi s =
        Set.univ.pi (Function.update s α Set.univ) ×ˢ s α := by
      ext ⟨x, y⟩
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
      constructor
      · intro h
        refine ⟨fun β => ?_, by simpa using h α⟩
        by_cases hβ : β = α
        · subst hβ; simp
        · simpa [Function.update_of_ne hβ] using h β
      · rintro ⟨h1, h2⟩ β
        by_cases hβ : β = α
        · subst hβ; simpa using h2
        · simpa [Function.update_of_ne hβ] using h1 β
    rw [hpre, Measure.prod_prod, interpLaw, Measure.pi_pi,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ α),
      ← Finset.mul_prod_erase Finset.univ
        (fun β => (Function.update (fun β => mixMeasure θ (ρ₀ β) (ρ₁ β)) α ρ β) (s β))
        (Finset.mem_univ α)]
    simp only [Function.update_self, measure_univ, one_mul]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun β hβ => ?_
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hβ)]
  rw [← hmap, integral_map hφ.aemeasurable hF.aestronglyMeasurable]

end Interpolation

/-- The sample space `ι → ℝ` of `X^θ`, carrying `interpLaw θ ρ₀ ρ₁`. -/
def InterpSpace (ι : Type) (_θ : ℝ) (_ρ₀ _ρ₁ : ι → Measure ℝ) : Type := ι → ℝ

instance (ι : Type) (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ) : MeasurableSpace (InterpSpace ι θ ρ₀ ρ₁) :=
  MeasurableSpace.pi

instance (ι : Type) [Fintype ι] (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ) :
    MeasureSpace (InterpSpace ι θ ρ₀ ρ₁) :=
  ⟨interpLaw θ ρ₀ ρ₁⟩

/-- The sample space `(ι → ℝ) × ℝ` of the pair `(X^θ, y)`, `y ∼ ρ` independent of `X^θ`. -/
def PairSpace (ι : Type) (_θ : ℝ) (_ρ₀ _ρ₁ : ι → Measure ℝ) (_ρ : Measure ℝ) : Type :=
  (ι → ℝ) × ℝ

instance (ι : Type) (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ) (ρ : Measure ℝ) :
    MeasurableSpace (PairSpace ι θ ρ₀ ρ₁ ρ) := Prod.instMeasurableSpace

instance (ι : Type) [Fintype ι] (θ : ℝ) (ρ₀ ρ₁ : ι → Measure ℝ) (ρ : Measure ℝ) :
    MeasureSpace (PairSpace ι θ ρ₀ ρ₁ ρ) :=
  ⟨(interpLaw θ ρ₀ ρ₁).prod ρ⟩

/-! ## Instances of the statements at concrete laws

The laws are Dirac masses `δ₀`, `δ₁` on each coordinate, with `ι = Fin 2` and `F x = x 0 * x 1`,
or `ι = Fin 1` and `F x = x 0` for (interpol), where both sides evaluate to `1`. -/

section Examples

-- `isProbabilityMeasure_mixMeasure` at `θ = 2`, outside `[0, 1]`.
example : IsProbabilityMeasure (mixMeasure 2 (Measure.dirac (0 : ℝ)) (Measure.dirac 1)) :=
  isProbabilityMeasure_mixMeasure _ _ _

-- `integral_mixMeasure` at `ρ₀ = ρ₁ = δ₀`, `f = id`, `θ = 1/2`.
example : ∫ x, x ∂(mixMeasure (1 / 2) (Measure.dirac (0 : ℝ)) (Measure.dirac 0)) =
    1 / 2 * ∫ x, x ∂(Measure.dirac (0 : ℝ)) + (1 - 1 / 2) * ∫ x, x ∂(Measure.dirac (0 : ℝ)) :=
  integral_mixMeasure (by norm_num) (by norm_num) (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top)

-- `integral_mixMeasure` at `ρ₀ = δ₀`, `ρ₁ = δ₁`, `f = id`, `θ = 1/3`: the mean of `ρ^θ` is `θ`.
example : ∫ x, x ∂(mixMeasure (1 / 3) (Measure.dirac (0 : ℝ)) (Measure.dirac 1)) = 1 / 3 := by
  rw [integral_mixMeasure (by norm_num) (by norm_num) (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top)]
  simp

end Examples

end Anisotropic
