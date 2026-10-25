import Anisotropic.Density.Count
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Eigen
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.Framework.Model
import Anisotropic.GeneralT.Model
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Instances.Models
import Anisotropic.Rigidity.Defs
import Anisotropic.Wigner.Model

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # The GOE edge vector, the reference class, and the external hypotheses `H_cmp¹`, `H_TW¹` -/

/-- The GOE edge vector `N^{2/3}(μ_1 - 2, …, μ_l - 2)` of the display before Corollary 3.19,
with `μ_1 ≥ μ_2 ≥ ⋯` the eigenvalues of the GOE matrix `goeW N`. -/
def goeEdge (N l : ℕ) (ω : GOESpace N) : Fin l → ℝ :=
  fun i => (N : ℝ) ^ (2 / 3 : ℝ) * (sortedEig (goeW N ω) (i + 1) - 2)

/-- The GOE edge vector is measurable. -/
theorem measurable_goeEdge (N l : ℕ) : Measurable (goeEdge N l) := by
  have hW : Continuous fun ω : Fin N × Fin N → ℝ => goeW N ω :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (min i j, max i j)
  have hH : ∀ ω : Fin N × Fin N → ℝ,
      goeW N ω ∈ {A : Matrix (Fin N) (Fin N) ℝ | A.IsHermitian} := fun ω => by
    show (goeW N ω)ᴴ = goeW N ω
    rw [conjTranspose_eq_transpose_of_trivial]
    exact (isGOE_goeW N).symm ω
  refine measurable_pi_iff.mpr fun i => ?_
  have hl : LipschitzOnWith 1 (fun A : Matrix (Fin N) (Fin N) ℝ => sortedEig A (i + 1))
      {A | A.IsHermitian} := by
    refine LipschitzOnWith.of_dist_le_mul fun A hA B hB => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact sortedEig_lipschitz hA hB (i + 1)
  have hc : Continuous fun ω : Fin N × Fin N → ℝ => sortedEig (goeW N ω) (i + 1) :=
    hl.continuousOn.comp_continuous hW hH
  exact (continuous_const.mul (hc.sub continuous_const)).measurable

/-- The law of the GOE edge vector on `ℝ^l`. -/
def goeEdgeLaw (N l : ℕ) : ProbabilityMeasure (Fin l → ℝ) :=
  ⟨(ℙ : Measure (GOESpace N)).map (goeEdge N l),
    (Measure.isProbabilityMeasure_map_iff (measurable_goeEdge N l).aemeasurable).mpr
      inferInstance⟩

/-- The reference class of the comparison with the GOE: `σ ≥ 0`, (bound_Sigma) `σ_i ≤ τ⁻¹`,
(Sigma_gap) `#{i : σ_i ∈ [0, τ]} ≤ (1 - τ) M`, (phi_bounded) `τ ≤ M/N ≤ τ⁻¹`, and the
rightmost edge `k = 1` regular (Definition 2.7 (i)). -/
structure RefClass (τ : ℝ) (M N : ℕ) (σ : Fin M → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ σ i
  le : ∀ i, σ i ≤ τ⁻¹
  gap : ({i | σ i ∈ Set.Icc 0 τ}.ncard : ℝ) ≤ (1 - τ) * M
  ratio_ge : τ ≤ (M : ℝ) / N
  ratio_le : (M : ℝ) / N ≤ τ⁻¹
  edge : RegularEdge τ N σ 1

/-- The external hypothesis `H_cmp¹`, the Gaussian case of Corollary 3.19 (i) at `β = 1` (the
works cited before the display of `q_l^β`): for every bounded Lipschitz `h`, the Gaussian
reference value `bRef N σ 1 l h` and `E h` of the GOE edge vector differ by at most `ε` for
`N ≥ N₀`, uniformly over the reference class. -/
def HCmp1 (τ : ℝ) (l : ℕ) : Prop :=
  ∀ (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (M : ℕ) (σ : Fin M → ℝ), RefClass τ M N σ →
      |(bRef N σ 1 l h) - (∫ ω, h (goeEdge N l ω))| ≤ ε

/-- The external hypothesis `H_TW¹`, the display before Corollary 3.19 at `β = 1`: the law of the
GOE edge vector converges weakly to a probability measure `q_l^1` on `ℝ^l`. -/
def HTW1 (l : ℕ) : Prop :=
  ∃ ν : ProbabilityMeasure (Fin l → ℝ), Tendsto (fun N => goeEdgeLaw N l) atTop (𝓝 ν)

/-- Under (T_diag), the spectrum of `Σ` of a model with edge `1` regular lies in the reference
class. -/
theorem refClass_of_isModel {Ω : Type} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hm : IsModel τ C M N Sig X) (hk : RegularEdge τ N (specOf Sig) 1) :
    RefClass τ M N (specOf Sig) := by
  have he := specOf_eq hm.sigma.posDef.isHermitian
  refine ⟨fun i => ?_, fun i => ?_, ?_, hm.ratio_ge, hm.ratio_le, hk⟩
  · rw [he]; exact (hm.sigma.posDef.eigenvalues_pos i).le
  · rw [he]; exact hm.sigma.eigenvalues_le i
  · rw [he]; exact hm.sigma.gap

/-- For a general `T`, the spectrum of `Σ = T Tᵀ` of a model with edge `1` regular lies in the
reference class. -/
theorem refClass_of_isModelT {Ω : Type} [MeasureSpace Ω] {τ : ℝ} {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hm : IsModelT τ C M K N T X) (hk : RegularEdge τ N (specOf (T * Tᵀ)) 1) :
    RefClass τ M N (specOf (T * Tᵀ)) := by
  have hp : (T * Tᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose T
  refine ⟨fun i => ?_, hm.eig_le, hm.gap, hm.ratio_ge, hm.ratio_le, hk⟩
  rw [specOf_eq hp.isHermitian]
  exact hp.eigenvalues_nonneg i

/-- The rate `K (B + L) N^{-1/(800(l+1))}` is eventually at most `ε`. -/
theorem edgeRate_eventually (K B : ℝ) (L : ℝ≥0) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) ≤ ε := by
  have hθ : (0 : ℝ) < 1 / (800 * (l + 1)) := by positivity
  have ht : Tendsto (fun N : ℕ => K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)))
      atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul
      (K * (B + L))
    simpa using this
  exact eventually_atTop.mp (ht.eventually (ge_mem_nhds hε))

/-- `X ↦ q_{k,l}` under (T_diag) is measurable along a measurable `X`. -/
theorem measurable_qVec_of_entries {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ}
    {Sig : Matrix (Fin M) (Fin M) ℝ} {X : Ω → Matrix (Fin M) (Fin N) ℝ}
    (hX : EntryAssumption C X) (l : ℕ) : Measurable fun ω => qVec Sig (X ω) 1 l := by
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hX.measurable i μ
  have hQ : Continuous fun Xm : Matrix (Fin M) (Fin N) ℝ => QN Sig Xm := by
    unfold QN; fun_prop
  exact (measurable_qVecA N (specOf Sig) N 1 l).comp (hQ.measurable.comp hXm)

/-- `X ↦ q_{k,l}` for a general `T` is measurable along a measurable `X`. -/
theorem measurable_qVecT_of_entries {Ω : Type} [MeasureSpace Ω] {C : ℕ → ℝ} {K : ℕ}
    {T : Matrix (Fin M) (Fin K) ℝ} {X : Ω → Matrix (Fin K) (Fin N) ℝ}
    (hX : EntryAssumption C X) (l : ℕ) : Measurable fun ω => qVecT T (X ω) 1 l := by
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hX.measurable i μ
  have hQ : Continuous fun Xm : Matrix (Fin K) (Fin N) ℝ => QN (Tᵀ * T) Xm := by
    unfold QN; fun_prop
  exact (measurable_qVecA N (specOf (T * Tᵀ)) N 1 l).comp (hQ.measurable.comp hXm)

/-- From a comparison with the GOE (for each bounded Lipschitz `f`, eventually in `N` and uniformly
over the models) and `γ_N → ν`, the laws converge to `ν` along every sequence with `N_n → ∞`. -/
theorem tendstoInDistribution_of_goeCmp {l : ℕ} (ν : ProbabilityMeasure (Fin l → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N l) atTop (𝓝 ν)) (Ns : ℕ → ℕ)
    (hN : Tendsto Ns atTop atTop) (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)]
    [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))] (q : ∀ n, Ω n → Fin l → ℝ)
    (hq : ∀ n, Measurable (q n))
    (hc : ∀ (f : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |f x| ≤ B) → LipschitzWith L f →
      ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, |(∫ ω, f (q n ω)) - (∫ ω, f (goeEdge (Ns n) l ω))| ≤ ε) :
    TendstoInDistribution q atTop id (fun n => (ℙ : Measure (Ω n))) (ν : Measure (Fin l → ℝ)) := by
  refine ⟨fun n => (hq n).aemeasurable, aemeasurable_id, ?_⟩
  refine tendsto_iff_forall_lipschitz_integral_tendsto.mpr ?_
  rintro f ⟨D, hD⟩ ⟨L, hL⟩
  have hB : ∀ x, |f x| ≤ |f 0| + D := fun x => by
    have h1 := hD x 0
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (f x) (f 0)
    linarith
  have hfm : AEStronglyMeasurable f := hL.continuous.aestronglyMeasurable
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id]
  have e1 : ∀ n, ∫ x, f x ∂(ℙ : Measure (Ω n)).map (q n) = ∫ ω, f (q n ω) := fun n =>
    integral_map (hq n).aemeasurable hL.continuous.aestronglyMeasurable
  simp_rw [e1]
  have hg := ((tendsto_iff_forall_lipschitz_integral_tendsto.mp htw) f ⟨D, hD⟩ ⟨L, hL⟩).comp hN
  have e2 : ∀ N, ∫ x, f x ∂(goeEdgeLaw N l : Measure (Fin l → ℝ)) = ∫ ω, f (goeEdge N l ω) :=
    fun N => integral_map (measurable_goeEdge N l).aemeasurable
      hL.continuous.aestronglyMeasurable
  have hg' : Tendsto (fun n => ∫ ω, f (goeEdge (Ns n) l ω)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure (Fin l → ℝ)))) := by
    refine hg.congr fun n => ?_
    simp only [Function.comp]
    exact e2 (Ns n)
  have hd : Tendsto (fun n => (∫ ω, f (q n ω)) - (∫ ω, f (goeEdge (Ns n) l ω))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hc f _ L hB hL (ε / 2) (half_pos hε)
    exact ⟨n₀, fun n hn => by
      rw [Real.dist_eq, sub_zero]
      exact (hn₀ n hn).trans_lt (half_lt_self hε)⟩
  simpa using hd.add hg'

/-- The reference class is inhabited at the Marchenko–Pastur point (`σ = 1`, `M = n`,
`N = 2n`) and at the singular point `σ = spec (tPad n tPad nᵀ)` (`M = N = 2n`). -/
example {n : ℕ} (hn : 0 < n) :
    RefClass (1 / 5) n (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
      RefClass (1 / 5) (2 * n) (2 * n) (specOf (tPad n * (tPad n)ᵀ)) := by
  have hk : RegularEdge (1 / 5) (2 * n) (specOf (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
    rw [specOf_one_eq]; exact regularEdge_mp hn
  exact ⟨refClass_of_isModel (isModel_radXn hn) hk,
    refClass_of_isModelT (isModelT_tPad hn) (mpT_hyps hn).2.2.1⟩

/-- The vector `q` of Corollary 3.19 is measurable for the Rademacher model with `Σ = 1`,
`M = n`, `N = 2n`. -/
example {n : ℕ} (hn : 0 < n) :
    Measurable fun ω => qVec (1 : Matrix (Fin n) (Fin n) ℝ) (radXn n ω) 1 1 :=
  measurable_qVec_of_entries (isModel_radXn hn).entries 1

/-- The vector `q` of Corollary 3.19 is measurable for the general-`T` model `T = tPad n`. -/
example {n : ℕ} (hn : 0 < n) :
    Measurable fun ω => qVecT (tPad n) (radXn n ω) 1 1 :=
  measurable_qVecT_of_entries (isModelT_tPad hn).entries 1

/-- The rate of Theorem 3.18 at `K = B = L = l = 1` is eventually at most `1/2`. -/
example : ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (1 : ℝ) * (1 + (1 : NNReal)) * (N : ℝ) ^ (-(1 / (800 * (((1 : ℕ) : ℝ) + 1)) : ℝ)) ≤ 1 / 2 :=
  edgeRate_eventually (ε := 1 / 2) 1 1 1 1 (by norm_num)

/-- The deduction of Corollary 3.19 (i) along the GOE sequence `N = n + 1` itself, with
`l = 1`; the convergence `γ_N → ν` stays a hypothesis. -/
example (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution (fun n => goeEdge (n + 1) 1) atTop id
      (fun n => (ℙ : Measure (GOESpace (n + 1)))) (ν : Measure (Fin 1 → ℝ)) :=
  tendstoInDistribution_of_goeCmp ν htw (fun n => n + 1) (tendsto_add_atTop_nat 1)
    (fun n => GOESpace (n + 1)) (fun n => goeEdge (n + 1) 1) (fun n => measurable_goeEdge _ _)
    (fun f B L hB hL ε hε => ⟨0, fun n _ => by simpa using hε.le⟩)

#print axioms goeEdge
#print axioms measurable_goeEdge
#print axioms goeEdgeLaw
#print axioms RefClass
#print axioms HCmp1
#print axioms HTW1
#print axioms refClass_of_isModel
#print axioms refClass_of_isModelT
#print axioms edgeRate_eventually
#print axioms measurable_qVec_of_entries
#print axioms measurable_qVecT_of_entries
#print axioms tendstoInDistribution_of_goeCmp

end Anisotropic
