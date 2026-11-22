module

public import Anisotropic.Entrywise.Defs
public import Anisotropic.LinAlg.Minor

@[expose] public section

/-!
# Independence and measurability of the minors `G^{(T)}`

For diagonal `Σ`, the minor `G^{(T)}` of Definition 4.3 is a measurable function of the entries
`X_{iμ}` with `i, μ ∉ T`. Hence it is independent of every family of entries of `X` lying in a
row or column of `T`. This is the independence behind the partial expectation `E_s` of
Section 5 (cond_exp).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M : ℕ}

/-! ## Independence and measurability of minors -/

/-- The determinant of a complex matrix with measurable entries is measurable. -/
private theorem measurable_det_of_entries {α : Type*} [MeasurableSpace α] {n : Type*} [Fintype n]
    [DecidableEq n] {A : α → Matrix n n ℂ} (hA : ∀ i j, Measurable fun a => A a i j) :
    Measurable fun a => (A a).det := by
  have hc : Continuous fun f : n → n → ℂ => (Matrix.of f).det :=
    Continuous.matrix_det (A := fun f : n → n → ℂ => Matrix.of f) continuous_id
  exact hc.measurable.comp
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hA i j)

/-- The entries of the inverse of a complex matrix with measurable entries are measurable
(with `A⁻¹ = 0` when `A` is singular). -/
private theorem measurable_inv_apply_of_entries {α : Type*} [MeasurableSpace α] {n : Type*}
    [Fintype n] [DecidableEq n] {A : α → Matrix n n ℂ} (hA : ∀ i j, Measurable fun a => A a i j)
    (i j : n) : Measurable fun a => (A a)⁻¹ i j := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  refine (measurable_det_of_entries hA).inv.mul ?_
  have hc : Continuous fun f : n → n → ℂ => (Matrix.of f).adjugate i j :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (Continuous.matrix_adjugate (A := fun f : n → n → ℂ => Matrix.of f) continuous_id))
  exact hc.measurable.comp
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hA i j)

/-- `G^{(T)}` depends only on the entries `X_{iμ}` with `i, μ ∉ T`. -/
private theorem Gm_congr_retained {N : ℕ} (Sig : Matrix (Fin M) (Fin M) ℝ)
    {X X' : Matrix (Fin M) (Fin N) ℝ} (z : ℂ) (T : Finset (Fin M ⊕ Fin N))
    (h : ∀ i μ, Sum.inl i ∉ T → Sum.inr μ ∉ T → X i μ = X' i μ) :
    Gm Sig X z T = Gm Sig X' z T := by
  have hH : minorH Sig X z T = minorH Sig X' z T := by
    ext ⟨u | u, hu⟩ ⟨v | v, hv⟩
    · simp [minorH, H, linH]
    · simp [minorH, H, linH, h u v hu hv]
    · simp [minorH, H, linH, h v u hv hu]
    · simp [minorH, H, linH]
  ext s t
  simp only [Gm, minorG, hH]

/-- The entries of `G^{(T)}` (zero-extended to `𝓘 × 𝓘`, `Σ = diag(σ)`) are measurable functions
of `ω` when the entries of `X` are. -/
theorem measurable_Gm_apply {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (σ : Fin M → ℝ)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : ∀ i μ, Measurable fun ω => X ω i μ) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) (s t : Fin M ⊕ Fin N) :
    Measurable fun ω => Gm (diagonal σ) (X ω) z T s t := by
  simp only [Gm, minorG]
  by_cases hs : s ∈ T
  · simp only [hs, dite_true]
    exact measurable_const
  · by_cases ht : t ∈ T
    · simp only [hs, ht, dite_true, dite_false]
      exact measurable_const
    · simp only [hs, ht, dite_false]
      refine measurable_inv_apply_of_entries (fun u v => ?_) _ _
      rcases u with ⟨u | u, hu⟩ <;> rcases v with ⟨v | v, hv⟩ <;>
        simp only [minorH, H, linH, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
          fromBlocks_apply₂₁, fromBlocks_apply₂₂, cplx, map_apply, transpose_apply] <;>
        first
        | exact measurable_const
        | exact Complex.measurable_ofReal.comp (hX _ _)

/-- Row/column entries of `X` in rows or columns of `T` are independent of `G^{(T)}`. -/
theorem indep_entries_minor {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {C : ℕ → ℝ} {N : ℕ} {σ : Fin M → ℝ} (hσ : ∀ i, 0 < σ i)
    {X : Ω → Matrix (Fin M) (Fin N) ℝ} (hX : EntryAssumption C X) (z : ℂ)
    (T : Finset (Fin M ⊕ Fin N)) (P : Finset (Fin M × Fin N))
    (hP : ∀ p ∈ P, Sum.inl p.1 ∈ T ∨ Sum.inr p.2 ∈ T) :
    IndepFun (fun ω (p : P) => X ω p.1.1 p.1.2)
      (fun ω (st : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) => Gm (diagonal σ) (X ω) z T st.1 st.2)
      ℙ := by
  set A : Finset (Fin M × Fin N) :=
    Finset.univ.filter (fun p => Sum.inl p.1 ∉ T ∧ Sum.inr p.2 ∉ T) with hAdef
  have hdisj : Disjoint P A := by
    rw [Finset.disjoint_left]
    intro p hp hpA
    simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hpA
    rcases hP p hp with h | h
    · exact hpA.1 h
    · exact hpA.2 h
  have hind := hX.indep.indepFun_finset P A hdisj (fun p => hX.measurable p.1 p.2)
  let fill : (A → ℝ) → Matrix (Fin M) (Fin N) ℝ :=
    fun y i μ => if h : (i, μ) ∈ A then y ⟨(i, μ), h⟩ else 0
  have hfill : ∀ i μ, Measurable fun y : A → ℝ => fill y i μ := by
    intro i μ
    by_cases h : (i, μ) ∈ A
    · simp only [fill, h, dite_true]
      exact measurable_pi_apply _
    · simp only [fill, h, dite_false]
      exact measurable_const
  have hψ : Measurable fun (y : A → ℝ) (st : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) =>
      Gm (diagonal σ) (fill y) z T st.1 st.2 :=
    Measurable.of_eval fun st => measurable_Gm_apply σ hfill z T st.1 st.2
  have hfun : (fun ω (st : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) =>
      Gm (diagonal σ) (X ω) z T st.1 st.2)
      = (fun (y : A → ℝ) (st : (Fin M ⊕ Fin N) × (Fin M ⊕ Fin N)) =>
          Gm (diagonal σ) (fill y) z T st.1 st.2) ∘ (fun ω (q : A) => X ω q.1.1 q.1.2) := by
    funext ω st
    simp only [Function.comp_apply]
    rw [Gm_congr_retained _ _ _ fun i μ hi hμ => ?_]
    have hmem : (i, μ) ∈ A := by simp [hAdef, hi, hμ]
    simp [fill, hmem]
  rw [hfun]
  exact hind.comp measurable_id hψ

/-! ## Compiled checks at the Rademacher instance `M = N = 2`, `σ ≡ 1`, `z = 2i` -/

section Checks

open Complex

end Checks

end Anisotropic

#print axioms Anisotropic.indep_entries_minor
#print axioms Anisotropic.measurable_Gm_apply
