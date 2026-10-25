import Anisotropic.Density.Count
import Anisotropic.EdgeUniv.Defs
import Anisotropic.EdgeUniv.Main
import Anisotropic.EdgeUniv.RegS
import Anisotropic.Entrywise.DiagModel
import Anisotropic.Framework.Domination
import Anisotropic.GeneralT.Model
import Anisotropic.Instances.Models

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Theorem 3.18 for general `T` -/

/-! ## Continuity of the rescaled eigenvalues -/

/-- For symmetric `A, B`, `|λ_j(A) - λ_j(B)| ≤ ‖A - B‖` for the eigenvalues `specOf` (Weyl). -/
private lemma generalT_specOf_lipschitz {K : ℕ} {A B : Matrix (Fin K) (Fin K) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (j : Fin K) :
    |specOf A j - specOf B j| ≤ ‖A - B‖ := by
  set i : Fin (Fintype.card (Fin K)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j
  have key : ∀ (C : Matrix (Fin K) (Fin K) ℝ) (hC : C.IsHermitian),
      specOf C j = sortedEig C ((i : ℕ) + 1) := by
    intro C hC
    rw [specOf_eq hC]
    unfold sortedEig
    rw [dite_eq_left_of_eq_true (eq_true ⟨hC, by omega, by have := i.isLt; omega⟩)]
    rfl
  rw [key A hA, key B hB]
  exact sortedEig_lipschitz hA hB _

/-- `Q_N = Xᵀ S X` is symmetric for symmetric `S`. -/
private lemma generalT_QN_herm {K : ℕ} {S : Matrix (Fin K) (Fin K) ℝ} (hS : S.IsHermitian)
    (Xm : Matrix (Fin K) (Fin N) ℝ) : (QN S Xm).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul Xm hS
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- `Xm ↦ Xmᵀ S Xm` is measurable. -/
private lemma generalT_measurable_QN {K : ℕ} (S : Matrix (Fin K) (Fin K) ℝ) :
    Measurable fun Xm : Matrix (Fin K) (Fin N) ℝ => QN S Xm :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul
    continuous_id).measurable

/-- `‖Xᵀ S X - Xᵀ S' X‖ ≤ ‖Xᵀ‖ ‖S - S'‖ ‖X‖`. -/
private lemma generalT_norm_QN_sub_le {K : ℕ} (S S' : Matrix (Fin K) (Fin K) ℝ)
    (Xm : Matrix (Fin K) (Fin N) ℝ) :
    ‖QN S Xm - QN S' Xm‖ ≤ ‖Xmᵀ‖ * ‖S - S'‖ * ‖Xm‖ := by
  have e : QN S Xm - QN S' Xm = Xmᵀ * (S - S') * Xm := by
    simp only [QN, Matrix.mul_sub, Matrix.sub_mul]
  rw [e]
  calc ‖Xmᵀ * (S - S') * Xm‖ ≤ ‖Xmᵀ * (S - S')‖ * ‖Xm‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Xmᵀ‖ * ‖S - S'‖ * ‖Xm‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)

/-- If `‖S_n - S‖ ≤ κ_n → 0`, then `‖Xᵀ S_n X - Xᵀ S X‖ → 0`. -/
private lemma generalT_QN_tendsto {K : ℕ} {Ss : ℕ → Matrix (Fin K) (Fin K) ℝ}
    {S : Matrix (Fin K) (Fin K) ℝ} {κs : ℕ → ℝ} (hle : ∀ n, ‖Ss n - S‖ ≤ κs n)
    (hκ : Tendsto κs atTop (𝓝 0)) (Xm : Matrix (Fin K) (Fin N) ℝ) :
    Tendsto (fun n => ‖QN (Ss n) Xm - QN S Xm‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ‖Xmᵀ‖ * κs n * ‖Xm‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hκ).mul (tendsto_const_nhds (x := ‖Xm‖))
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  refine (generalT_norm_QN_sub_le _ _ _).trans ?_
  have := hle n
  gcongr

/-- The vectors `q_{l_n,l}(A_n)` built from the data `σ_n` converge to `q_{k,l}(A)` built from
`σ` when the sign and the indices agree, the edges and the scales converge (the limit scale is
nonzero), and `‖A_n - A‖ → 0`. -/
private lemma generalT_qVecA_tendsto {K M' n : ℕ} {σs : ℕ → Fin K → ℝ} {ls : ℕ → ℕ}
    {σ : Fin M' → ℝ} {k l : ℕ} {As : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hAs : ∀ m, (As m).IsHermitian) (hA : A.IsHermitian)
    (hsign : ∀ m, edgeSign (ls m) = edgeSign k)
    (hidx : ∀ m i, edgeIdx N (σs m) (ls m) i = edgeIdx N σ k i)
    (hval : Tendsto (fun m => edgeVal N (σs m) (ls m)) atTop (𝓝 (edgeVal N σ k)))
    (hscale : Tendsto (fun m => edgeScale N (σs m) (ls m)) atTop (𝓝 (edgeScale N σ k)))
    (hϖ : edgeScale N σ k ≠ 0) (hconv : Tendsto (fun m => ‖As m - A‖) atTop (𝓝 0)) :
    Tendsto (fun m => qVecA N (σs m) (As m) (ls m) l) atTop (𝓝 (qVecA N σ A k l)) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  unfold qVecA
  simp_rw [hsign, hidx]
  have heig : Tendsto (fun m => sortedEig (As m) (edgeIdx N σ k (i + 1))) atTop
      (𝓝 (sortedEig A (edgeIdx N σ k (i + 1)))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun m => dist_nonneg)
      (fun m => by rw [Real.dist_eq]; exact sortedEig_lipschitz (hAs m) hA _) hconv
  exact (tendsto_const_nhds.div hscale hϖ).mul (heig.sub hval)

/-- `q_{k,l}` depends on `σ` only through its nonzero values with multiplicity. -/
private lemma generalT_qVecA_nzEq {K n : ℕ} {σ : Fin M → ℝ} {σ' : Fin K → ℝ} (h : NzEq σ σ')
    (N : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k l : ℕ) : qVecA N σ' A k l = qVecA N σ A k l := by
  funext i
  unfold qVecA edgeIdx
  rw [h.cumCount_eq N, h.edgeVal_eq N, h.edgeScale_eq N]

/-! ## Two analytic facts -/

/-- Dominated convergence on a probability space with a constant bound. -/
private lemma generalT_integral_tendsto {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {B : ℝ}
    (hF : ∀ m, Measurable (F m)) (hB : ∀ m ω, |F m ω| ≤ B)
    (hlim : ∀ ω, Tendsto (fun m => F m ω) atTop (𝓝 (f ω))) :
    Tendsto (fun m => ∫ ω, F m ω) atTop (𝓝 (∫ ω, f ω)) :=
  tendsto_integral_of_dominated_convergence (fun _ => B) (fun m => (hF m).aestronglyMeasurable)
    (integrable_const B)
    (fun m => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB m ω)
    (Eventually.of_forall hlim)

/-- On a probability space, `|E f(Y) - E g(Y)| ≤ δ` for bounded measurable `f, g` with
`|f - g| ≤ δ`. -/
private lemma generalT_integral_sub_le {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {l : ℕ} {Y : Ω → Fin l → ℝ} (hY : Measurable Y)
    {f g : (Fin l → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) {B δ : ℝ}
    (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B) (hfg : ∀ x, |f x - g x| ≤ δ) :
    |(∫ ω, f (Y ω)) - ∫ ω, g (Y ω)| ≤ δ := by
  have hfi : Integrable (fun ω => f (Y ω)) :=
    Integrable.of_bound (hf.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _)
  have hgi : Integrable (fun ω => g (Y ω)) :=
    Integrable.of_bound (hg.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgB _)
  rw [← integral_sub hfi hgi]
  have := norm_integral_le_of_norm_le_const (μ := (ℙ : Measure Ω))
    (f := fun ω => f (Y ω) - g (Y ω)) (C := δ)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfg _)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

/-- The rate `K (B + L) N^{-1/(800(l+1))}` is eventually at most `ε`. -/
private lemma generalT_rate_eventually (K B : ℝ) (L : ℝ≥0) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) ≤ ε := by
  have hθ : (0 : ℝ) < 1 / (800 * (l + 1)) := by positivity
  have ht : Tendsto (fun N : ℕ => K * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)))
      atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul
      (K * (B + L))
    simpa using this
  exact eventually_atTop.mp (ht.eventually (ge_mem_nhds hε))

/-! ## Theorem 3.18 for general `T` -/

/-- Theorem 3.18 for a general `T` (§11.1), bounded Lipschitz `h`, with rate. -/
theorem edge_univT_lip (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (hτ : 0 < τ) :
    ∃ K₀ : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω]
      [IsProbabilityMeasure (ℙ : Measure Ω)] (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ)
      (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      ∀ (h : (Fin l → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0), (∀ x, |h x| ≤ B) → LipschitzWith L h →
        |(∫ ω, h (qVecT T (X ω) k l)) - bRef N (specOf (T * Tᵀ)) k l h| ≤
          K₀ * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := by
  have hτ3 : 0 < τ ^ 3 := pow_pos hτ 3
  have hτE : 0 < tauE τ := lt_min hτ3 (by linarith)
  obtain ⟨K₁, N₁, h₁⟩ := edge_univ_lip (tauE τ) C l hτE
  refine ⟨K₁, N₁, ?_⟩
  intro N hN Ω _ _ M K T X k hm hk h B L hB hL
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := hm.ratio_ge
      rw [h0, Nat.cast_zero, div_zero] at this
      linarith
    · exact h0
  have hda := hm.densityAssumptions hτ
  have hPS : (Tᵀ * T).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self T
  have hSH := hPS.isHermitian
  have hnz := nzEq_specOf_mul_transpose T
  -- a sequence `κ_n ↓ 0` with edges `l_n` of `Ŝ + κ_n P₀` whose data converge to those of `k`
  have hseq : ∀ n : ℕ, ∃ κ : ℝ, 0 < κ ∧ κ ≤ τ ^ 3 ∧ κ < 1 / ((n : ℝ) + 1) ∧
      ∃ l', RegularEdge (tauE τ) N (specOf (regS κ (Tᵀ * T))) l' ∧
        edgeSign l' = edgeSign k ∧
        (∀ i, edgeIdx N (specOf (regS κ (Tᵀ * T))) l' i = edgeIdx N (specOf (T * Tᵀ)) k i) ∧
        |edgeVal N (specOf (regS κ (Tᵀ * T))) l' - edgeVal N (specOf (T * Tᵀ)) k| ≤
          1 / ((n : ℝ) + 1) ∧
        |edgeScale N (specOf (regS κ (Tᵀ * T))) l' - edgeScale N (specOf (T * Tᵀ)) k| ≤
          1 / ((n : ℝ) + 1) := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have ev := regS_edge_transfer hτ hN1 hda hm.ratioK_le hk hδ
    have ev2 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ τ ^ 3 ∧ κ < 1 / ((n : ℝ) + 1) := by
      have e1 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ := self_mem_nhdsWithin
      have e2 : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ < min (τ ^ 3) (1 / ((n : ℝ) + 1)) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hτ3 hδ))
      filter_upwards [e1, e2] with κ hκ1 hκ2
      exact ⟨hκ1, (lt_of_lt_of_le hκ2 (min_le_left _ _)).le,
        lt_of_lt_of_le hκ2 (min_le_right _ _)⟩
    obtain ⟨κ, ⟨h1, h2, h3⟩, hl⟩ := (ev2.and ev).exists
    exact ⟨κ, h1, h2, h3, hl⟩
  choose κs hκ0 hκτ hκn ls hreg hsign hidx hval hscale using hseq
  -- the bound of Theorem 3.18 under (T_diag) for `(Ŝ + κ_n P₀, X)` at `τ_E`
  have hbd : ∀ n, |(∫ ω, h (qVec (regS (κs n) (Tᵀ * T)) (X ω) (ls n) l)) -
      bRef N (specOf (regS (κs n) (Tᵀ * T))) (ls n) l h| ≤
        K₁ * (B + L) * (N : ℝ) ^ (-(1 / (800 * (l + 1)) : ℝ)) := fun n =>
    h₁ N hN K (regS (κs n) (Tᵀ * T)) X (ls n)
      ((isModel_regS hτ hm (hκ0 n) (hκτ n)).mono hτE (min_le_left _ _)) (hreg n) h B L hB hL
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hκlim : Tendsto κs atTop (𝓝 0) :=
    squeeze_zero (fun n => (hκ0 n).le) (fun n => (hκn n).le) h1n
  have hval' : Tendsto (fun n => edgeVal N (specOf (regS (κs n) (Tᵀ * T))) (ls n)) atTop
      (𝓝 (edgeVal N (specOf (T * Tᵀ)) k)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact hval n) h1n
  have hscale' : Tendsto (fun n => edgeScale N (specOf (regS (κs n) (Tᵀ * T))) (ls n)) atTop
      (𝓝 (edgeScale N (specOf (T * Tᵀ)) k)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact hscale n)
      h1n
  have hϖ : edgeScale N (specOf (T * Tᵀ)) k ≠ 0 := (edgeScale_bounds hda hk).1.ne'
  have hRH : ∀ n, (regS (κs n) (Tᵀ * T)).IsHermitian := fun n =>
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate _ _)
  have hnorm : ∀ n, ‖regS (κs n) (Tᵀ * T) - Tᵀ * T‖ ≤ κs n := fun n =>
    regS_norm_sub_le (hκ0 n).le hPS
  have hhm : Measurable h := hL.continuous.measurable
  -- the model side: `E h(q^{κ_n}) → E h(q)`
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  have hmodel : Tendsto (fun n => ∫ ω, h (qVec (regS (κs n) (Tᵀ * T)) (X ω) (ls n) l)) atTop
      (𝓝 (∫ ω, h (qVecT T (X ω) k l))) := by
    refine generalT_integral_tendsto (B := B)
      (fun n => hhm.comp ((measurable_qVecA _ _ _ _ _).comp
        ((generalT_measurable_QN _).comp hXm))) (fun n ω => hB _) (fun ω => ?_)
    exact (hL.continuous.tendsto _).comp
      (generalT_qVecA_tendsto (fun n => generalT_QN_herm (hRH n) _) (generalT_QN_herm hSH _)
        hsign hidx hval' hscale' hϖ (generalT_QN_tendsto hnorm hκlim _))
  -- the reference side: `b_N(h, spec(Ŝ + κ_n P₀)) → b_N(h, spec Σ)`
  have hσ' : ∀ j, 0 ≤ specOf (Tᵀ * T) j := fun j => by
    rw [specOf_eq hSH]
    exact hPS.eigenvalues_nonneg j
  have hdiag : ∀ n, ‖diagonal (specOf (regS (κs n) (Tᵀ * T))) - diagonal (specOf (Tᵀ * T))‖ ≤
      κs n := by
    intro n
    rw [diagonal_sub, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (hκ0 n).le).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact (generalT_specOf_lipschitz (hRH n) hSH j).trans (hnorm n)
  have hGm : Measurable (gaussX K N) := (gaussX_isGaussianEnsemble K N).measurable_mat
  have hlimref : bRef N (specOf (T * Tᵀ)) k l h = ∫ ω, h (qVecA N (specOf (T * Tᵀ))
      (QN (diagonal (specOf (Tᵀ * T))) (gaussX K N ω)) k l) := by
    rw [bRef_nzEq hnz hda.nonneg hσ' N k l hhm]
    unfold bRef
    simp_rw [generalT_qVecA_nzEq hnz]
  have href : Tendsto (fun n => bRef N (specOf (regS (κs n) (Tᵀ * T))) (ls n) l h) atTop
      (𝓝 (bRef N (specOf (T * Tᵀ)) k l h)) := by
    rw [hlimref]
    unfold bRef
    refine generalT_integral_tendsto (B := B)
      (fun n => hhm.comp ((measurable_qVecA _ _ _ _ _).comp
        ((generalT_measurable_QN _).comp hGm))) (fun n ω => hB _) (fun ω => ?_)
    exact (hL.continuous.tendsto _).comp
      (generalT_qVecA_tendsto (fun n => generalT_QN_herm (isHermitian_diagonal _) _)
        (generalT_QN_herm (isHermitian_diagonal _) _) hsign hidx hval' hscale' hϖ
        (generalT_QN_tendsto hdiag hκlim _))
  exact le_of_tendsto' (hmodel.sub href).abs hbd

/-- Theorem 3.18 (`thm:edge_univ`) for a general `T` (§11.1), bounded uniformly continuous `h`. -/
theorem edge_univT (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (ε : ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ) (k : ℕ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      |(∫ ω, h (qVecT T (X ω) k l)) - bRef N (specOf (T * Tᵀ)) k l h| ≤ ε := by
  obtain ⟨B, hB⟩ := hb
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, L, hgL, hgB, hhg⟩ := exists_lipschitz_approx hB hu hε3
  obtain ⟨K₀, N₀, hK⟩ := edge_univT_lip τ C l hτ
  obtain ⟨N₁, hN₁⟩ := generalT_rate_eventually K₀ B L l hε3
  refine ⟨max N₀ N₁, fun N hN Ω _ _ M K T X k hm hk => ?_⟩
  have hhm : Measurable h := hu.continuous.measurable
  have hgm : Measurable g := hgL.continuous.measurable
  have hXm : Measurable X :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun μ => hm.entries.measurable i μ
  have hGm : Measurable (gaussX M N) := (gaussX_isGaussianEnsemble M N).measurable_mat
  have hY : Measurable fun ω => qVecT T (X ω) k l :=
    (measurable_qVecA N (specOf (T * Tᵀ)) N k l).comp ((generalT_measurable_QN _).comp hXm)
  have hY0 : Measurable fun ω =>
      qVecA N (specOf (T * Tᵀ)) (QN (diagonal (specOf (T * Tᵀ))) (gaussX M N ω)) k l :=
    (measurable_qVecA N (specOf (T * Tᵀ)) N k l).comp ((generalT_measurable_QN _).comp hGm)
  have e1 := generalT_integral_sub_le hY hhm hgm hB hgB hhg
  have e2 := (hK N (le_of_max_le_left hN) M K T X k hm hk g B L hgB hgL).trans
    (hN₁ N (le_of_max_le_right hN))
  have e3 : |bRef N (specOf (T * Tᵀ)) k l g - bRef N (specOf (T * Tᵀ)) k l h| ≤ ε / 3 := by
    unfold bRef
    exact generalT_integral_sub_le hY0 hgm hhm hgB hB
      (fun x => by rw [abs_sub_comm]; exact hhg x)
  have := abs_add_three ((∫ ω, h (qVecT T (X ω) k l)) - ∫ ω, g (qVecT T (X ω) k l))
    ((∫ ω, g (qVecT T (X ω) k l)) - bRef N (specOf (T * Tᵀ)) k l g)
    (bRef N (specOf (T * Tᵀ)) k l g - bRef N (specOf (T * Tᵀ)) k l h)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at this
  linarith

/-! ## Instances -/

/-- The clamp `x ↦ max(-1, min(x₁, 1))` is bounded by `1` and `1`-Lipschitz. -/
private theorem clamp_bounded_lipschitz :
    (∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1) ∧
      LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
  refine ⟨fun x => abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩, ?_⟩
  exact ((LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).min_const 1).const_max (-1)

/-- Theorem 3.18 for a general `T` at `T = (I_n; 0)` (`Σ = T Tᵀ` singular, `M = 2n`, `K = n`,
`N = 2n`), the clamp of the top eigenvalue. -/
example : ∃ K₀ : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    |(∫ ω, max (-1) (min (qVecT (tPad n) (radXn n ω) 1 1 0) 1)) -
        bRef (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 1 (fun x => max (-1) (min (x 0) 1))| ≤
      K₀ * (1 + 1) * ((2 * n : ℕ) : ℝ) ^ (-(1 / (800 * (1 + 1)) : ℝ)) := by
  obtain ⟨K₀, N₀, h⟩ := edge_univT_lip (1 / 5) (fun _ => 1) 1 (by norm_num)
  refine ⟨K₀, N₀, fun n hn hN => ?_⟩
  have := h (2 * n) hN (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn) (mpT_hyps hn).2.2.1
    (fun x => max (-1) (min (x 0) 1)) 1 1 clamp_bounded_lipschitz.1 clamp_bounded_lipschitz.2
  simpa using this

/-- Theorem 3.18 for a general `T` and bounded uniformly continuous `h` at `T = (I_n; 0)`
(`M = 2n`, `K = n`, `N = 2n`), for the clamp of the top eigenvalue and the precision
`ε = 1/10`. -/
example : ∃ N₀ : ℕ, ∀ n : ℕ, 0 < n → N₀ ≤ 2 * n →
    |(∫ ω, max (-1) (min (qVecT (tPad n) (radXn n ω) 1 1 0) 1)) -
        bRef (2 * n) (specOf (tPad n * (tPad n)ᵀ)) 1 1 (fun x => max (-1) (min (x 0) 1))| ≤
      1 / 10 := by
  obtain ⟨N₀, h⟩ := edge_univT (1 / 5) (fun _ => 1) 1 (fun x => max (-1) (min (x 0) 1)) (1 / 10)
    (by norm_num) ⟨1, clamp_bounded_lipschitz.1⟩ clamp_bounded_lipschitz.2.uniformContinuous
    (by norm_num)
  refine ⟨N₀, fun n hn hN => ?_⟩
  exact h (2 * n) hN (2 * n) n (tPad n) (radXn n) 1 (isModelT_tPad hn) (mpT_hyps hn).2.2.1

/-- Theorem 3.18 for a general `T`, the paper's form: there is `b_N(h, π)`, depending only on
`N` and the nonzero eigenvalues of `Σ = T Tᵀ` with multiplicity (not on the dimensions of `T`),
such that `E h(q_{k,l}) - b_N(h, π) → 0` along every sequence of models with `N → ∞` and the
edge `k_n` regular. -/
example (τ : ℝ) (C : ℕ → ℝ) (l : ℕ) (h : (Fin l → ℝ) → ℝ) (hτ : 0 < τ)
    (hb : ∃ B, ∀ x, |h x| ≤ B) (hu : UniformContinuous h) :
    ∃ b : (N : ℕ) → (M : ℕ) → (Fin M → ℝ) → ℕ → ℝ,
      (∀ (N M M' : ℕ) (σ : Fin M → ℝ) (σ' : Fin M' → ℝ) (k : ℕ), NzEq σ σ' →
          (∀ i, 0 ≤ σ i) → (∀ j, 0 ≤ σ' j) → b N M σ k = b N M' σ' k) ∧
      ∀ (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
        (Ms Ks Ns : ℕ → ℕ) (T : ∀ n, Matrix (Fin (Ms n)) (Fin (Ks n)) ℝ)
        (X : ∀ n, Ω n → Matrix (Fin (Ks n)) (Fin (Ns n)) ℝ) (k : ℕ → ℕ),
        Tendsto Ns atTop atTop →
        (∀ n, IsModelT τ C (Ms n) (Ks n) (Ns n) (T n) (X n)) →
        (∀ n, RegularEdge τ (Ns n) (specOf (T n * (T n)ᵀ)) (k n)) →
        Tendsto (fun n => (∫ ω, h (qVecT (T n) (X n ω) (k n) l)) -
          b (Ns n) (Ms n) (specOf (T n * (T n)ᵀ)) (k n)) atTop (𝓝 0) := by
  refine ⟨fun N M σ k => bRef N σ k l h, fun N M M' σ σ' k hz hσ hσ' =>
    bRef_nzEq hz hσ hσ' N k l hu.continuous.measurable, ?_⟩
  intro Ω _ _ Ms Ks Ns T X k hNs hm hk
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := edge_univT τ C l h (ε / 2) hτ hb hu (half_pos hε)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hNs.eventually_ge_atTop N₀)
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hN₀ (Ns n) (hn₀ n hn) (Ms n) (Ks n) (T n) (X n) (k n) (hm n) (hk n)).trans_lt
    (half_lt_self hε)

/-- The sequence hypotheses of the paper's form for a general `T` hold together along the
family `T_n = (I_{n+1}; 0)`, `M_n = N_n = 2(n + 1)`, `K_n = n + 1`, Rademacher entries,
`k_n = 1`, `τ = 1/5`, `C ≡ 1`. -/
example :
    Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop ∧
      (∀ n : ℕ, IsModelT (Ω := SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) (1 / 5)
        (fun _ => 1) (2 * (n + 1)) (n + 1) (2 * (n + 1)) (tPad (n + 1)) (radXn (n + 1))) ∧
      ∀ n : ℕ, RegularEdge (1 / 5) (2 * (n + 1)) (specOf (tPad (n + 1) * (tPad (n + 1))ᵀ)) 1 :=
  ⟨tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id,
    fun n => isModelT_tPad n.succ_pos, fun n => (mpT_hyps n.succ_pos).2.2.1⟩

#print axioms edge_univT_lip
#print axioms edge_univT

end Anisotropic
