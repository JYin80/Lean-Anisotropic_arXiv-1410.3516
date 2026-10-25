import Anisotropic.Comparison.Interpolation
import Anisotropic.Framework.Domination
import Anisotropic.Wigner.GOE
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

/-! # Entry laws and the interpolation between `W` and the GOE -/

/-- The law of the upper-triangular entry `α` of `W`. -/
def entryLawW {Ω : Type*} [MeasureSpace Ω] {N : ℕ} (W : Ω → Matrix (Fin N) (Fin N) ℝ)
    (α : UpperIdx N) : Measure ℝ :=
  (ℙ : Measure Ω).map fun ω => W ω α.1.1 α.1.2

/-- The GOE law of the entry `α`. -/
def goeLaw (N : ℕ) (α : UpperIdx N) : Measure ℝ := gaussianReal 0 (goeVar N α.1)

/-- The symmetric matrix with upper-triangular coordinates `x`. -/
def ofUpper {N : ℕ} (x : UpperIdx N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => x ⟨(min i j, max i j), min_le_max⟩

/-! ## Laws of the entries -/

/-- The moment, mean and variance conditions of the class, for a single law on `ℝ`; the variance
lies in `[lo, hi]`. -/
private structure ULaw (N : ℕ) (C : ℕ → ℝ) (lo hi : ℝ) (ν : Measure ℝ) : Prop where
  integrable : ∀ p : ℕ, Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν
  mean : ∫ x, x ∂ν = 0
  var_ge : lo ≤ ∫ x, x ^ 2 ∂ν
  var_le : ∫ x, x ^ 2 ∂ν ≤ hi
  moment : ∀ p : ℕ, ∫ x, |Real.sqrt N * x| ^ p ∂ν ≤ C p

/-- The upper index `(min i j, max i j)` of the entry `(i, j)`. -/
private def upIdx {N : ℕ} (i j : Fin N) : UpperIdx N := ⟨(min i j, max i j), min_le_max⟩

/-- The variance bound of the entry `α`: `2/N` on the diagonal and `1/N` off it. -/
private def varHi (N : ℕ) (α : UpperIdx N) : ℝ := if α.1.1 = α.1.2 then 2 / (N : ℝ) else 1 / N

private instance goeLaw_isProbabilityMeasure (N : ℕ) (α : UpperIdx N) :
    IsProbabilityMeasure (goeLaw N α) := by
  unfold goeLaw
  infer_instance

private lemma entryLawW_isProbabilityMeasure {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {N : ℕ} {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : ∀ i j, Measurable fun ω => W ω i j) (α : UpperIdx N) :
    IsProbabilityMeasure (entryLawW W α) :=
  ⟨by simp [entryLawW, Measure.map_apply (hW α.1.1 α.1.2) MeasurableSet.univ]⟩

/-- The entry law `α` of a matrix in the class satisfies the conditions of `ULaw`. -/
private lemma entryLawW_uLaw {Ω : Type*} [MeasureSpace Ω] {C : ℕ → ℝ} {N : ℕ}
    {W : Ω → Matrix (Fin N) (Fin N) ℝ} (hW : WigClassEntries C N W) (α : UpperIdx N) :
    ULaw N C (1 / N) (varHi N α) (entryLawW W α) := by
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
    · simp only [varHi, h, ite_true]
      exact hW.var_diag_le _
    · simp only [varHi, h, ite_false]
      exact (hW.var_off _ _ h).le
  · exact (key (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le (hW.moment p _ _)

/-- The entry law of the GOE matrix `goeW N` is `goeLaw N`. -/
private lemma entryLawW_goeW (N : ℕ) (α : UpperIdx N) : entryLawW (goeW N) α = goeLaw N α := by
  obtain ⟨⟨i, j⟩, hij⟩ := α
  change i ≤ j at hij
  simp only [entryLawW, goeLaw]
  rcases hij.lt_or_eq with h | h
  · rw [(isGOE_goeW N).law_off i j h]
    simp [goeVar, h.ne]
  · subst h
    rw [(isGOE_goeW N).law_diag i]
    simp [goeVar]

/-- The law `goeLaw N α` of a GOE entry satisfies the conditions of `ULaw`. -/
private lemma goeLaw_uLaw {N : ℕ} (hN : 1 ≤ N) (α : UpperIdx N) :
    ULaw N (fun p => (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p) (1 / N) (varHi N α)
      (goeLaw N α) := by
  rw [← entryLawW_goeW]
  exact entryLawW_uLaw ((isGOE_goeW N).classEntries hN) α

/-- Integrability of `|√N x|^p` gives integrability of `x^p`. -/
private lemma integrable_pow_of_sqrt {N : ℕ} (hN : 1 ≤ N) {ν : Measure ℝ} {p : ℕ}
    (h : Integrable (fun x : ℝ => |Real.sqrt N * x| ^ p) ν) :
    Integrable (fun x : ℝ => x ^ p) ν := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine (h.const_mul ((Real.sqrt N)⁻¹ ^ p)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hs, mul_pow, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hs.ne', one_pow, one_mul]

private lemma integrable_mixMeasure {θ : ℝ} {ρ₀ ρ₁ : Measure ℝ} {f : ℝ → ℝ}
    (hf₀ : Integrable f ρ₀) (hf₁ : Integrable f ρ₁) : Integrable f (mixMeasure θ ρ₀ ρ₁) :=
  (hf₁.smul_measure ENNReal.ofReal_ne_top).add_measure (hf₀.smul_measure ENNReal.ofReal_ne_top)

/-- A mixture of two laws satisfying `ULaw` satisfies `ULaw` with the larger moment function. -/
private lemma ULaw.mix {N : ℕ} (hN : 1 ≤ N) {C₀ C₁ : ℕ → ℝ} {lo hi : ℝ} {ν₀ ν₁ : Measure ℝ}
    (h₀ : ULaw N C₀ lo hi ν₀) (h₁ : ULaw N C₁ lo hi ν₁) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ULaw N (fun p => max (C₁ p) (C₀ p)) lo hi (mixMeasure θ ν₀ ν₁) := by
  have hi : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ p) ν₀ ∧ Integrable (fun x : ℝ => x ^ p) ν₁ :=
    fun p => ⟨integrable_pow_of_sqrt hN (h₀.integrable p),
      integrable_pow_of_sqrt hN (h₁.integrable p)⟩
  have hvar := integral_mixMeasure hθ₀ hθ₁ (hi 2).1 (hi 2).2
  have hc : 0 ≤ 1 - θ := sub_nonneg.2 hθ₁
  refine ⟨fun p => integrable_mixMeasure (h₀.integrable p) (h₁.integrable p), ?_, ?_, ?_,
    fun p => ?_⟩
  · have e := integral_mixMeasure hθ₀ hθ₁ (by simpa using (hi 1).1) (by simpa using (hi 1).2)
    rw [e, h₀.mean, h₁.mean]
    ring
  · rw [hvar]
    nlinarith [mul_le_mul_of_nonneg_left h₁.var_ge hθ₀, mul_le_mul_of_nonneg_left h₀.var_ge hc]
  · rw [hvar]
    nlinarith [mul_le_mul_of_nonneg_left h₁.var_le hθ₀, mul_le_mul_of_nonneg_left h₀.var_le hc]
  · rw [integral_mixMeasure hθ₀ hθ₁ (h₀.integrable p) (h₁.integrable p)]
    have a := (h₁.moment p).trans (le_max_left (C₁ p) (C₀ p))
    have b := (h₀.moment p).trans (le_max_right (C₁ p) (C₀ p))
    nlinarith [mul_le_mul_of_nonneg_left a hθ₀, mul_le_mul_of_nonneg_left b hc]

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

/-! ## The interpolants -/

/-- The interpolants `W^θ` (Definition 7.6 with `ι = {i ≤ j}`, `ρ⁰ =` GOE, `ρ¹ =` law of `W`)
belong to the class with moments `momMaxW C`. -/
theorem wigClass_interp {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    WigClassEntries (momMaxW C)
      (Ω := InterpSpace (UpperIdx N) θ (goeLaw N) (entryLawW W)) N ofUpper := by
  have : ∀ α, IsProbabilityMeasure (entryLawW W α) :=
    entryLawW_isProbabilityMeasure hW.measurable
  have : ∀ α, IsProbabilityMeasure (goeLaw N α) := fun α => inferInstance
  have : ∀ α : UpperIdx N, IsProbabilityMeasure (mixMeasure θ (goeLaw N α) (entryLawW W α)) :=
    fun α => isProbabilityMeasure_mixMeasure θ _ _
  have hP : ∀ α : UpperIdx N, ULaw N (momMaxW C) (1 / N) (varHi N α)
      (mixMeasure θ (goeLaw N α) (entryLawW W α)) := fun α =>
    (goeLaw_uLaw hN α).mix hN (entryLawW_uLaw hW α) h₀ h₁
  have key : ∀ (i j : Fin N) (f : ℝ → ℝ), Continuous f →
      ∫ ω, f (ofUpper ω i j) ∂(interpLaw θ (goeLaw N) (entryLawW W)) =
        ∫ x, f x ∂(mixMeasure θ (goeLaw N (upIdx i j)) (entryLawW W (upIdx i j))) :=
    fun i j f hf =>
      integral_interp_coord θ (goeLaw N) (entryLawW W) (upIdx i j) hf.aestronglyMeasurable
  refine ⟨fun i j => measurable_pi_apply (X := fun _ : UpperIdx N => ℝ) (upIdx i j),
    fun ω => ?_, ?_, fun i j => ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_,
    fun p i j => ?_, fun p i j => ?_⟩
  · ext i j
    simp [ofUpper, min_comm, max_comm]
  · have h := iIndepFun_pi
      (μ := fun α : UpperIdx N => mixMeasure θ (goeLaw N α) (entryLawW W α))
      (X := fun _ x => x) fun _ => aemeasurable_id
    have e : (fun (p : UpperIdx N) (ω : UpperIdx N → ℝ) => ofUpper ω p.1.1 p.1.2) =
        fun p ω => ω p := by
      funext p ω
      simp [ofUpper, min_eq_left p.2, max_eq_right p.2]
    change iIndepFun (fun (p : UpperIdx N) (ω : UpperIdx N → ℝ) => ofUpper ω p.1.1 p.1.2)
      (Measure.pi fun α : UpperIdx N => mixMeasure θ (goeLaw N α) (entryLawW W α))
    rw [e]
    exact h
  · exact (key i j (fun x => x) continuous_id).trans (hP (upIdx i j)).mean
  · have hv := hP (upIdx i j)
    have hne : (upIdx i j).1.1 ≠ (upIdx i j).1.2 := fun h =>
      hij (le_antisymm ((le_max_left i j).trans (h.symm.le.trans (min_le_right i j)))
        ((le_max_right i j).trans (h.symm.le.trans (min_le_left i j))))
    have e := key i j (fun x => x ^ 2) (by fun_prop)
    have hle : ∫ x, x ^ 2 ∂(mixMeasure θ (goeLaw N (upIdx i j)) (entryLawW W (upIdx i j))) ≤
        1 / (N : ℝ) := by
      have := hv.var_le
      rwa [varHi, if_neg hne] at this
    exact e.trans (le_antisymm hle hv.var_ge)
  · have e := key i i (fun x => x ^ 2) (by fun_prop)
    exact (hP (upIdx i i)).var_ge.trans_eq e.symm
  · have e := key i i (fun x => x ^ 2) (by fun_prop)
    have hv : varHi N (upIdx i i) = 2 / (N : ℝ) := by simp [varHi, upIdx]
    exact e.trans_le (hv ▸ (hP (upIdx i i)).var_le)
  · exact integrable_interp_coord θ (goeLaw N) (entryLawW W) (upIdx i j)
      (f := fun x : ℝ => |Real.sqrt N * x| ^ p) ((hP (upIdx i j)).integrable p)
  · exact (key i j (fun x => |Real.sqrt N * x| ^ p) (by fun_prop)).trans_le
      ((hP (upIdx i j)).moment p)

/-- The interpolants `W^θ` have vanishing third moments when `W` has. -/
theorem zeroThirdW_interp {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {W : Ω → Matrix (Fin N) (Fin N) ℝ}
    (hW : WigClassEntries C N W) (h3 : ∀ i j, ∫ ω, W ω i j ^ 3 = 0) {θ : ℝ} (h₀ : 0 ≤ θ)
    (h₁ : θ ≤ 1) :
    ∀ i j, ∫ x, (ofUpper x : Matrix (Fin N) (Fin N) ℝ) i j ^ 3
      ∂(interpLaw θ (goeLaw N) (entryLawW W)) = 0 := by
  have : ∀ α, IsProbabilityMeasure (entryLawW W α) :=
    entryLawW_isProbabilityMeasure hW.measurable
  have : ∀ α, IsProbabilityMeasure (goeLaw N α) := fun α => inferInstance
  intro i j
  have hm : AEMeasurable (fun ω => W ω (upIdx i j).1.1 (upIdx i j).1.2) (ℙ : Measure Ω) :=
    (hW.measurable _ _).aemeasurable
  have h1 : ∫ x, x ^ 3 ∂(entryLawW W (upIdx i j)) = 0 :=
    (integral_map hm (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable).trans
      (h3 _ _)
  have h0 : ∫ x, x ^ 3 ∂(goeLaw N (upIdx i j)) = 0 := integral_cube_gaussianReal _
  have hi₀ := integrable_pow_of_sqrt hN ((goeLaw_uLaw hN (upIdx i j)).integrable 3)
  have hi₁ := integrable_pow_of_sqrt hN ((entryLawW_uLaw hW (upIdx i j)).integrable 3)
  have e := integral_interp_coord θ (goeLaw N) (entryLawW W) (upIdx i j)
    (f := fun x : ℝ => x ^ 3) (by fun_prop : Continuous fun x : ℝ => x ^ 3).aestronglyMeasurable
  change ∫ ω, (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) i j ^ 3
    ∂(interpLaw θ (goeLaw N) (entryLawW W)) = 0
  rw [show (fun ω : UpperIdx N → ℝ => (ofUpper ω : Matrix (Fin N) (Fin N) ℝ) i j ^ 3) =
      fun ω => (fun x : ℝ => x ^ 3) (ω (upIdx i j)) from rfl, e,
    integral_mixMeasure h₀ h₁ hi₀ hi₁, h1, h0]
  ring

/-! ## Instances -/

/-- `ofUpper` is symmetric (`N = 2`). -/
example (x : UpperIdx 2 → ℝ) : (ofUpper x : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = ofUpper x 0 1 := by
  simp [ofUpper, min_comm, max_comm]

/-- The interpolant between the GOE (`N = 2`) and the Rademacher Wigner matrix at `θ = 1/2`
lies in the class with moments `momMaxW (fun _ => 1)`. -/
example : WigClassEntries (momMaxW fun _ => 1)
    (Ω := InterpSpace (UpperIdx 2) (1 / 2) (goeLaw 2) (entryLawW (wigRad 2))) 2 ofUpper :=
  wigClass_interp (by norm_num) (wignerEntries_wigRad (by norm_num)).toClass (by norm_num)
    (by norm_num)

/-- The same interpolant has vanishing third moments, since the Rademacher entries do. -/
example : ∀ i j, ∫ x, (ofUpper x : Matrix (Fin 2) (Fin 2) ℝ) i j ^ 3
      ∂(interpLaw (1 / 2) (goeLaw 2) (entryLawW (wigRad 2))) = 0 :=
  zeroThirdW_interp (by norm_num) (wignerEntries_wigRad (by norm_num)).toClass
    (wigRad_third 2) (by norm_num) (by norm_num)

/-- The endpoint `θ = 0` with `W` the GOE (`N = 3`). -/
example : WigClassEntries (momMaxW fun p => (2 : ℝ) ^ ((p : ℝ) / 2) * gaussMoment p)
    (Ω := InterpSpace (UpperIdx 3) 0 (goeLaw 3) (entryLawW (goeW 3))) 3 ofUpper :=
  wigClass_interp (by norm_num) ((isGOE_goeW 3).classEntries (by norm_num)) le_rfl
    zero_le_one

#print axioms entryLawW
#print axioms goeLaw
#print axioms ofUpper
#print axioms wigClass_interp
#print axioms zeroThirdW_interp

end Anisotropic
