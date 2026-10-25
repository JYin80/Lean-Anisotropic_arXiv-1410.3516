import Anisotropic.Probability.LDE.Main

/-!
# Large deviation estimates with coefficients independent of the family

The large deviation estimates of `Anisotropic.Probability.LDE.Main` in the form in which the
paper applies them (Section 5, proof of Lemma 5.2, estimate (Gij_estimate), and the
analogous steps of the later sections): the coefficients are `a (Y ω)` for a measurable `Y`
independent of the whole family `(x_i)_i`, and the bound is evaluated at the same random
coefficients.

* `lde_linear_cond`, `lde_offdiag_cond`, `lde_diag_cond`: the linear, off-diagonal and diagonal
  estimates with coefficients independent of the family;
* `lde_bilinear_cond`: `|∑_{μ,ν} x_μ B_μν x'_ν| ≺ (∑_{μ,ν} |B_μν|²)^{1/2}/N` for two disjoint
  families `x`, `x'` forming one row family, as in (Gij_estimate).

Proof: the law of `(x, Y)` is the product of the laws of `x` and `Y`, so the probability of the
bad event is the `Y`-average of the probabilities of its slices; each slice is the bad event of
the deterministic estimate at a fixed coefficient, with the same threshold `N₀`. The bilinear
estimate is the off-diagonal one for the joint family with the block coefficient matrix that
vanishes on the two diagonal blocks.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace Anisotropic

/-! ## Slice bound under independence -/

/-- If `ξ` and `Y` are independent and every slice `{ω | (ξ ω, b) ∈ S}` has probability at most
`c`, then so does `{ω | (ξ ω, Y ω) ∈ S}`. -/
private lemma cond_slice {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {E β : Type*} [MeasurableSpace E] [MeasurableSpace β] {ξ : Ω → E} {Y : Ω → β}
    (hξ : Measurable ξ) (hY : Measurable Y) (hind : IndepFun ξ Y ℙ) {S : Set (E × β)}
    (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : ∀ b, ℙ {ω | (ξ ω, b) ∈ S} ≤ c) :
    ℙ {ω | (ξ ω, Y ω) ∈ S} ≤ c := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hξ.aemeasurable hY.aemeasurable).1 hind
  calc ℙ {ω | (ξ ω, Y ω) ∈ S} = (ℙ : Measure Ω).map (fun ω => (ξ ω, Y ω)) S :=
        (Measure.map_apply (hξ.prodMk hY) hS).symm
    _ = (((ℙ : Measure Ω).map ξ).prod ((ℙ : Measure Ω).map Y)) S := by rw [hmap]
    _ = ∫⁻ b, (ℙ : Measure Ω).map ξ ((fun t => (t, b)) ⁻¹' S) ∂((ℙ : Measure Ω).map Y) :=
        Measure.prod_apply_symm hS
    _ ≤ ∫⁻ _, c ∂((ℙ : Measure Ω).map Y) := lintegral_mono fun b => by
        rw [Measure.map_apply hξ (measurable_prodMk_right hS)]
        exact hc b
    _ = c := by simp

/-! ## The conditional estimates -/

section LDEpins

/-- Linear estimate with coefficients `a (Y ω)`, `Y` independent of the family `x`. -/
theorem lde_linear_cond (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι β : Type} [Fintype ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
      (a : β → ι → ℂ), RowAssumption C N x → Measurable Y →
      (∀ i, Measurable fun b => a b i) → IndepFun (fun ω i => x i ω) Y ℙ →
      DomAt N ε D (fun ω => ‖∑ i, a (Y ω) i * x i ω‖) (fun ω => ldeLinBound N (a (Y ω))) := by
  obtain ⟨N₀, h⟩ := lde_linear C hε D
  refine ⟨N₀, fun N hN Ω _ _ ι β _ _ x Y a hx hY ha hind => ?_⟩
  have hξ : Measurable fun ω (i : ι) => x i ω := Measurable.of_eval hx.measurable
  have hS : MeasurableSet {p : (ι → ℝ) × β |
      (N : ℝ) ^ ε * ldeLinBound N (a p.2) < ‖∑ i, a p.2 i * (p.1 i : ℂ)‖} := by
    refine measurableSet_lt ?_ ?_
    · unfold ldeLinBound
      fun_prop
    · fun_prop
  exact cond_slice hξ hY hind hS fun b => h N hN x hx (a b)

/-- Off-diagonal estimate with coefficients `A (Y ω)`, `Y` independent of the family `x`. -/
theorem lde_offdiag_cond (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι β : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace β] (x : ι → Ω → ℝ)
      (Y : Ω → β) (A : β → ι → ι → ℂ), RowAssumption C N x → Measurable Y →
      (∀ i j, Measurable fun b => A b i j) → IndepFun (fun ω i => x i ω) Y ℙ →
      DomAt N ε D (fun ω => ‖∑ i, ∑ j ∈ Finset.univ.erase i, x i ω * A (Y ω) i j * x j ω‖)
        (fun ω => ldeOffBound N (A (Y ω))) := by
  obtain ⟨N₀, h⟩ := lde_offdiag C hε D
  refine ⟨N₀, fun N hN Ω _ _ ι β _ _ _ x Y A hx hY hA hind => ?_⟩
  have hξ : Measurable fun ω (i : ι) => x i ω := Measurable.of_eval hx.measurable
  have hS : MeasurableSet {p : (ι → ℝ) × β | (N : ℝ) ^ ε * ldeOffBound N (A p.2) <
      ‖∑ i, ∑ j ∈ Finset.univ.erase i, (p.1 i : ℂ) * A p.2 i j * (p.1 j : ℂ)‖} := by
    refine measurableSet_lt ?_ ?_
    · unfold ldeOffBound
      fun_prop
    · fun_prop
  exact cond_slice hξ hY hind hS fun b => h N hN x hx (A b)

/-- Diagonal estimate with coefficients `a (Y ω)`, `Y` independent of the family `x`. -/
theorem lde_diag_cond (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι β : Type} [Fintype ι] [MeasurableSpace β] (x : ι → Ω → ℝ) (Y : Ω → β)
      (a : β → ι → ℂ), RowAssumption C N x → Measurable Y →
      (∀ i, Measurable fun b => a b i) → IndepFun (fun ω i => x i ω) Y ℙ →
      DomAt N ε D (fun ω => ‖∑ i, a (Y ω) i * (x i ω ^ 2 - 1 / (N : ℝ))‖)
        (fun ω => ldeDiagBound N (a (Y ω))) := by
  obtain ⟨N₀, h⟩ := lde_diag C hε D
  refine ⟨N₀, fun N hN Ω _ _ ι β _ _ x Y a hx hY ha hind => ?_⟩
  have hξ : Measurable fun ω (i : ι) => x i ω := Measurable.of_eval hx.measurable
  have hS : MeasurableSet {p : (ι → ℝ) × β | (N : ℝ) ^ ε * ldeDiagBound N (a p.2) <
      ‖∑ i, a p.2 i * ((p.1 i : ℂ) ^ 2 - 1 / ((N : ℝ) : ℂ))‖} := by
    refine measurableSet_lt ?_ ?_
    · unfold ldeDiagBound
      fun_prop
    · fun_prop
  exact cond_slice hξ hY hind hS fun b => h N hN x hx (a b)

/-- Bilinear estimate (Gij_estimate): `x` and `x'` jointly a row family (as `Sum.elim`),
`|∑_{μ,ν} x_μ B_μν x'_ν| ≺ (∑|B_μν|²)^{1/2}/N`, coefficients independent of `(x, x')`. -/
theorem lde_bilinear_cond (C : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {ι κ β : Type} [Fintype ι] [Fintype κ] [MeasurableSpace β] (x : ι → Ω → ℝ)
      (x' : κ → Ω → ℝ) (Y : Ω → β) (B : β → ι → κ → ℂ),
      RowAssumption C N (Sum.elim x x') → Measurable Y →
      (∀ i j, Measurable fun b => B b i j) →
      IndepFun (fun ω (s : ι ⊕ κ) => Sum.elim x x' s ω) Y ℙ →
      DomAt N ε D (fun ω => ‖∑ i, ∑ j, x i ω * B (Y ω) i j * x' j ω‖)
        (fun ω => Real.sqrt (∑ i, ∑ j, ‖B (Y ω) i j‖ ^ 2) / N) := by
  classical
  obtain ⟨N₀, h⟩ := lde_offdiag_cond C hε D
  refine ⟨N₀, fun N hN Ω _ _ ι κ β _ _ _ x x' Y B hx hY hB hind => ?_⟩
  let A : β → ι ⊕ κ → ι ⊕ κ → ℂ := fun b =>
    Sum.elim (fun i => Sum.elim (fun _ => 0) (fun j => B b i j)) (fun _ _ => 0)
  have hA : ∀ s t, Measurable fun b => A b s t := by
    rintro (i | k) (j | l)
    · exact measurable_const
    · exact hB i l
    · exact measurable_const
    · exact measurable_const
  have hdiag : ∀ b s, A b s s = 0 := by
    intro b s
    cases s <;> rfl
  have key := h N hN (Sum.elim x x') Y A hx hY hA hind
  have hstat : ∀ ω, ∑ s, ∑ t ∈ Finset.univ.erase s,
      (Sum.elim x x' s ω : ℂ) * A (Y ω) s t * (Sum.elim x x' t ω : ℂ) =
      ∑ i, ∑ j, (x i ω : ℂ) * B (Y ω) i j * (x' j ω : ℂ) := by
    intro ω
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_erase _ (by rw [hdiag, mul_zero, zero_mul])]
    simp [A, Fintype.sum_sum_type]
  have hbound : ∀ b, ldeOffBound N (A b) = Real.sqrt (∑ i, ∑ j, ‖B b i j‖ ^ 2) / N := by
    intro b
    unfold ldeOffBound
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_erase _ (by rw [hdiag, norm_zero,
      zero_pow two_ne_zero])]
    simp [A, Fintype.sum_sum_type]
  unfold DomAt at key ⊢
  simpa only [hstat, hbound] using key

end LDEpins



#print axioms lde_linear_cond
#print axioms lde_offdiag_cond
#print axioms lde_diag_cond
#print axioms lde_bilinear_cond

end Anisotropic
