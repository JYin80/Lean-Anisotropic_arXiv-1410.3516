module

public import Anisotropic.EdgeUniv.GOEEdge
public import Anisotropic.EdgeUniv.Main
public import Anisotropic.Entrywise.DiagModel
public import Anisotropic.GeneralT.Model
public import Anisotropic.Instances.MarchenkoPastur
public import Anisotropic.Instances.MarchenkoPasturTwo
public import Anisotropic.Instances.Models

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The reference class at a regular edge `k`, the external hypothesis `H_cmp^{1,e}`, and Corollary 3.19 (ii) for `β = 1`, `l = 1` under (T_diag) -/

/-- The reference class at the edge `k`: `σ ≥ 0`, (bound_Sigma) `σ_i ≤ τ⁻¹`,
(Sigma_gap) `#{i : σ_i ∈ [0, τ]} ≤ (1 - τ) M`, (phi_bounded) `τ ≤ M/N ≤ τ⁻¹`, and the edge `k`
regular (Definition 2.7 (i)). -/
structure RefClassE (τ : ℝ) (M N : ℕ) (σ : Fin M → ℝ) (k : ℕ) : Prop where
  nonneg : ∀ i, 0 ≤ σ i
  le : ∀ i, σ i ≤ τ⁻¹
  gap : ({i | σ i ∈ Set.Icc 0 τ}.ncard : ℝ) ≤ (1 - τ) * M
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  edge : RegularEdge τ N σ k

/-- At the rightmost edge `k = 1` the reference class is `RefClass`. -/
theorem refClassE_one_iff {τ : ℝ} {σ : Fin M → ℝ} :
    RefClassE τ M N σ 1 ↔ RefClass τ M N σ :=
  ⟨fun h => ⟨h.nonneg, h.le, h.gap, h.ratio_ge, h.ratio_le, h.edge⟩,
    fun h => ⟨h.nonneg, h.le, h.gap, h.ratio_ge, h.ratio_le, h.edge⟩⟩

/-- Under (T_diag), the spectrum of `Σ` of a model with edge `k` regular lies in the reference
class at `k`. -/
theorem refClassE_of_isModel {Ω : Type} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {k : ℕ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) (hk : RegularEdge τ N (specOf Sig) k) :
    RefClassE τ M N (specOf Sig) k := by
  have he := specOf_eq hm.sigma.posDef.isHermitian
  refine ⟨fun i => ?_, fun i => ?_, ?_, hm.ratio_ge, hm.ratio_le, hk⟩
  · rw [he]; exact (hm.sigma.posDef.eigenvalues_pos i).le
  · rw [he]; exact hm.sigma.eigenvalues_le i
  · rw [he]; exact hm.sigma.gap

/-- For a general `T`, the spectrum of `Σ = T Tᵀ` of a model with edge `k` regular lies in the
reference class at `k`. -/
theorem refClassE_of_isModelT {Ω : Type} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {K k : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hm : IsModelT τ C M K N T X) (hk : RegularEdge τ N (specOf (T * Tᵀ)) k) :
    RefClassE τ M N (specOf (T * Tᵀ)) k := by
  have hp : (T * Tᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose T
  refine ⟨fun i => ?_, hm.eig_le, hm.gap, hm.ratio_ge, hm.ratio_le, hk⟩
  rw [specOf_eq hp.isHermitian]
  exact hp.eigenvalues_nonneg i

/-- The external hypothesis `H_cmp^{1,e}`, the Gaussian real case at the edge `k` with `l = 1`
(an extension of Corollary 3.19 (ii) to `β = 1`): for every bounded Lipschitz `h`, the Gaussian
reference value `bRef N σ k 1 h` and `E h` of the top GOE edge statistic `N^{2/3}(μ_1 - 2)` differ
by at most `ε` for `N ≥ N₀`, uniformly over the reference class at `k`. At an even `k` the
statistic `q_{k,1}` carries the sign `-1`, so the lowest eigenvalue of the component is compared
with `μ_1`. -/
def HCmp1E (τ : ℝ) (k : ℕ) : Prop :=
  ∀ (h : (Fin 1 → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), RefClassE τ M N σ k →
      |(bRef N σ k 1 h) - (∫ ω, h (goeEdge N 1 ω))| ≤ ε

/-- At the rightmost edge `k = 1`, `H_cmp^{1,e}` is `H_cmp¹` with `l = 1`. -/
theorem hCmp1E_one_iff (τ : ℝ) : HCmp1E τ 1 ↔ HCmp1 τ 1 := by
  constructor
  · intro H h B L hB hL ε hε
    obtain ⟨N₀, hN₀⟩ := H h B L hB hL ε hε
    exact ⟨N₀, fun N hN M σ hσ => hN₀ N hN M σ (refClassE_one_iff.mpr hσ)⟩
  · intro H h B L hB hL ε hε
    obtain ⟨N₀, hN₀⟩ := H h B L hB hL ε hε
    exact ⟨N₀, fun N hN M σ hσ => hN₀ N hN M σ (refClassE_one_iff.mp hσ)⟩

/-- `X ↦ q_{k,l}` under (T_diag) is measurable along a measurable `X`, at every edge `k`. -/
theorem measurable_qVec_of_entries' {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (k l : ℕ) : Measurable fun ω => qVec Sig (X ω) k l := by
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hX.measurable i μ
  have hQ : Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => QN Sig Xm := by
    unfold QN; fun_prop
  exact (measurable_qVecA N (specOf Sig) N k l).comp (hQ.measurable.comp hXm)

/-- `X ↦ q_{k,l}` for a general `T` is measurable along a measurable `X`, at every edge `k`. -/
theorem measurable_qVecT_of_entries' {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (k l : ℕ) : Measurable fun ω => qVecT T (X ω) k l := by
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hX.measurable i μ
  have hQ : Continuous fun Xm : Matrix (Fin K) (Fin N) ℝ => QN (Tᵀ * T) Xm := by
    unfold QN; fun_prop
  exact (measurable_qVecA N (specOf (T * Tᵀ)) N k l).comp (hQ.measurable.comp hXm)

/-- Corollary 3.19 (ii) (`cor:TWA`) for real `Q` (`β = 1`) and `l = 1`, under (T_diag), the
comparison form: under `H_cmp^{1,e}` at the edge `k`, for bounded Lipschitz `h`, `E h(q_{k,1})`
and `E h(N^{2/3}(μ_1 - 2))` differ by at most `ε` for `N ≥ N₀`, uniformly over the models with
edge `k` regular. -/
theorem twaE_cmp (τ : ℝ) (C : ℕ → ℝ) (k : ℕ) (hτ : 0 < τ) (hcmp : HCmp1E τ k)
    (h : (Fin 1 → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0) (hB : ∀ x, |h x| ≤ B) (hL : LipschitzWith L h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M : ℕ) (Sig : Matrix (Fin M) (Fin M) ℝ) (X : Ω → Matrix (Fin M) (Fin N) ℝ),
      IsModel τ C M N Sig X → RegularEdge τ N (specOf Sig) k →
      |(∫ ω, h (qVec Sig (X ω) k 1)) - (∫ ω, h (goeEdge N 1 ω))| ≤ ε := by
  obtain ⟨K, N₁, hK⟩ := edge_univ_lip τ C 1 hτ
  obtain ⟨N₂, hN₂⟩ := hcmp h B L hB hL (ε / 2) (half_pos hε)
  obtain ⟨N₃, hN₃⟩ := edgeRate_eventually K B L 1 (half_pos hε)
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M Sig X hm hk => ?_⟩
  have h1 := hK N (le_of_max_le_left hN) M Sig X k hm hk h B L hB hL
  have h2 := hN₂ N (le_of_max_le_left (le_of_max_le_right hN)) M (specOf Sig)
    (refClassE_of_isModel hm hk)
  have h3 := hN₃ N (le_of_max_le_right (le_of_max_le_right hN))
  calc |(∫ ω, h (qVec Sig (X ω) k 1)) - (∫ ω, h (goeEdge N 1 ω))|
      ≤ |(∫ ω, h (qVec Sig (X ω) k 1)) - bRef N (specOf Sig) k 1 h| +
        |(bRef N (specOf Sig) k 1 h) - (∫ ω, h (goeEdge N 1 ω))| := abs_sub_le _ _ _
    _ ≤ ε := by push_cast at h1 h3; linarith

/-- Corollary 3.19 (ii) (`cor:TWA`) for real `Q` (`β = 1`) and `l = 1`, under (T_diag), the
convergence form: under `H_cmp^{1,e}` at the edge `k` and `γ_N → ν` (`H_TW¹` at `l = 1`, with
limit `ν = q_1^1`), along every sequence of models with `N_n → ∞` and edge `k` regular,
`q_{k,1}` converges in distribution to `ν`. -/
theorem twaE_conv (τ : ℝ) (C : ℕ → ℝ) (k : ℕ) (hτ : 0 < τ) (hcmp : HCmp1E τ k)
    (ν : ProbabilityMeasure (Fin 1 → ℝ)) (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν))
    (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
    (Ms Ns : ℕ → ℕ) (Sig : ∀ n, Matrix (Fin (Ms n)) (Fin (Ms n)) ℝ)
    (X : ∀ n, Ω n → Matrix (Fin (Ms n)) (Fin (Ns n)) ℝ) (hN : Tendsto Ns atTop atTop)
    (hm : ∀ n, IsModel τ C (Ms n) (Ns n) (Sig n) (X n))
    (hk : ∀ n, RegularEdge τ (Ns n) (specOf (Sig n)) k) :
    TendstoInDistribution (fun n ω => qVec (Sig n) (X n ω) k 1) atTop id
      (fun n => (ℙ : Measure (Ω n))) (ν : Measure (Fin 1 → ℝ)) := by
  refine tendstoInDistribution_of_goeCmp ν htw Ns hN Ω _
    (fun n => measurable_qVec_of_entries' (hm n).entries k 1) ?_
  intro f B L hB hL ε hε
  obtain ⟨N₀, hN₀⟩ := twaE_cmp τ C k hτ hcmp f B L hB hL ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hN.eventually (eventually_ge_atTop N₀))
  exact ⟨n₀, fun n hn => hN₀ (Ns n) (hn₀ n hn) (Ms n) (Sig n) (X n) (hm n) (hk n)⟩

/-- The reference class at `k = 1` at the Marchenko–Pastur point (`σ = 1`, `M = n`, `N = 2n`),
and at both edges `k = 1, 2` at the point `σ = 1`, `M = 2n`, `N = n` (`φ = 2`, `τ = 1/20`). -/
example {n : ℕ} (hn : 0 < n) :
    RefClassE (1 / 5) n (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 ∧
      RefClassE (1 / 10 / 2) (2 * n) n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 1 ∧
      RefClassE (1 / 10 / 2) (2 * n) n (specOf (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) 2 := by
  have hm := (isModel_two hn).mono (by norm_num : (0 : ℝ) < 1 / 10 / 2) (by norm_num)
  refine ⟨refClassE_of_isModel (isModel_radXn hn) ?_, refClassE_of_isModel hm ?_,
    refClassE_of_isModel hm ?_⟩
  · rw [specOf_one_eq]; exact regularEdge_mp hn
  · rw [specOf_one_eq]; exact regularEdge_two hn le_rfl (by norm_num)
  · rw [specOf_one_eq]; exact regularEdge_two hn (by norm_num) le_rfl

/-- The bounded Lipschitz test function `x ↦ max (-1) (min (x 0) 1)`. -/
private theorem clamp_bdd : ∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1 := fun x => by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

private theorem clamp_lip : LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
  have h0 : LipschitzWith 1 (fun x : Fin 1 → ℝ => x 0) := LipschitzWith.eval (0 : Fin 1)
  have h1 : LipschitzWith 1 (fun x : Fin 1 → ℝ => min (x 0) 1) :=
    by simpa using h0.min (LipschitzWith.const (1 : ℝ))
  simpa using (LipschitzWith.const (-1 : ℝ)).max h1

/-- Corollary 3.19 (ii), `β = 1`, `l = 1`, under (T_diag) at the Marchenko–Pastur point
(`Σ = I`, `M_n = n + 1`, `N_n = 2(n + 1)`, Rademacher entries, edge `k = 1`): every
non-external hypothesis holds; `H_cmp^{1,e}` and `γ_N → ν` are hypotheses. -/
example (hcmp : HCmp1E (1 / 5) 1) (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution
      (fun n (ω : SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) =>
        qVec (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (radXn (n + 1) ω) 1 1)
      atTop id (fun n => (ℙ : Measure (SignSpace (Fin (n + 1) × Fin (2 * (n + 1))))))
      (ν : Measure (Fin 1 → ℝ)) := by
  have hN : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id
  refine twaE_conv (1 / 5) (fun _ => 1) 1 (by norm_num) hcmp ν htw
    (fun n => SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) (fun n => n + 1)
    (fun n => 2 * (n + 1)) (fun n => 1) (fun n => radXn (n + 1)) hN
    (fun n => isModel_radXn n.succ_pos) (fun n => ?_)
  rw [specOf_one_eq]
  exact regularEdge_mp n.succ_pos

/-- Corollary 3.19 (ii), `β = 1`, `l = 1`, under (T_diag) at the lower edge `k = 2` of the
point `Σ = I`, `M_n = 2(n + 1)`, `N_n = n + 1` (`φ = 2`, Gaussian entries, `τ = 1/20`): every
non-external hypothesis holds; `H_cmp^{1,e}` and `γ_N → ν` are hypotheses. -/
example (hcmp : HCmp1E (1 / 10 / 2) 2) (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution
      (fun n (ω : GaussSpace (2 * (n + 1)) (n + 1)) =>
        qVec (1 : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℝ)
          (gaussX (2 * (n + 1)) (n + 1) ω) 2 1)
      atTop id (fun n => (ℙ : Measure (GaussSpace (2 * (n + 1)) (n + 1))))
      (ν : Measure (Fin 1 → ℝ)) := by
  refine twaE_conv (1 / 10 / 2) gaussMoment 2 (by norm_num) hcmp ν htw
    (fun n => GaussSpace (2 * (n + 1)) (n + 1)) (fun n => 2 * (n + 1)) (fun n => n + 1)
    (fun n => 1) (fun n => gaussX (2 * (n + 1)) (n + 1)) (tendsto_add_atTop_nat 1)
    (fun n => (isModel_two (Nat.succ_pos n)).mono (by norm_num) (by norm_num)) (fun n => ?_)
  rw [specOf_one_eq]
  exact regularEdge_two n.succ_pos (by norm_num) le_rfl

/-- The comparison form of Corollary 3.19 (ii), `β = 1`, `l = 1`, under (T_diag) at the lower
edge `k = 2` of the point `Σ = I`, `M_n = 2(n + 1)`, `N_n = n + 1` (`φ = 2`, Gaussian entries,
`τ = 1/20`), for the nonconstant bounded Lipschitz test function `x ↦ max (-1) (min (x 0) 1)`;
`H_cmp^{1,e}` is a hypothesis. -/
example (hcmp : HCmp1E (1 / 10 / 2) 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      |(∫ ω : GaussSpace (2 * (n + 1)) (n + 1),
          max (-1) (min (qVec (1 : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℝ)
            (gaussX (2 * (n + 1)) (n + 1) ω) 2 1 0) 1)) -
        (∫ ω, max (-1) (min (goeEdge (n + 1) 1 ω 0) 1))| ≤ ε := by
  obtain ⟨N₀, hN₀⟩ := twaE_cmp (1 / 10 / 2) gaussMoment 2 (by norm_num) hcmp
    (fun x => max (-1) (min (x 0) 1)) 1 1 clamp_bdd clamp_lip ε hε
  refine ⟨N₀, fun n hn => hN₀ (n + 1) (by omega) (2 * (n + 1)) 1 (gaussX (2 * (n + 1)) (n + 1))
    ((isModel_two (Nat.succ_pos n)).mono (by norm_num) (by norm_num)) ?_⟩
  rw [specOf_one_eq]
  exact regularEdge_two n.succ_pos (by norm_num) le_rfl

#print axioms RefClassE
#print axioms refClassE_one_iff
#print axioms refClassE_of_isModel
#print axioms refClassE_of_isModelT
#print axioms HCmp1E
#print axioms hCmp1E_one_iff
#print axioms measurable_qVec_of_entries'
#print axioms measurable_qVecT_of_entries'
#print axioms twaE_cmp
#print axioms twaE_conv

end Anisotropic
