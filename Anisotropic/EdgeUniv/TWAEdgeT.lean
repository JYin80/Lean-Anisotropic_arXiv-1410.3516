import Anisotropic.EdgeUniv.GOEEdge
import Anisotropic.EdgeUniv.GeneralT
import Anisotropic.EdgeUniv.Main
import Anisotropic.EdgeUniv.TWAEdge
import Anisotropic.Endpoints.Resolvents
import Anisotropic.Entrywise.DiagModel
import Anisotropic.GeneralT.Model
import Anisotropic.Instances.MarchenkoPastur
import Anisotropic.Instances.MarchenkoPasturTwo
import Anisotropic.Instances.Models

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ProbabilityTheory ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section
open Classical

namespace Anisotropic

variable {M N : ℕ}

/-! # Corollary 3.19 (ii) for `β = 1`, `l = 1`, for a general `T` -/

/-- The bounded Lipschitz test function `x ↦ max (-1) (min (x 0) 1)`. -/
private theorem clampT_bdd : ∀ x : Fin 1 → ℝ, |max (-1) (min (x 0) 1)| ≤ 1 := fun x => by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

private theorem clampT_lip : LipschitzWith 1 (fun x : Fin 1 → ℝ => max (-1) (min (x 0) 1)) := by
  have h0 : LipschitzWith 1 (fun x : Fin 1 → ℝ => x 0) := LipschitzWith.eval (0 : Fin 1)
  have h1 : LipschitzWith 1 (fun x : Fin 1 → ℝ => min (x 0) 1) :=
    by simpa using h0.min (LipschitzWith.const (1 : ℝ))
  simpa using (LipschitzWith.const (-1 : ℝ)).max h1

/-- `Σ = T Tᵀ = I` for `T = I^{1/2}`. -/
private theorem sigPow_one_mul_transpose (m : ℕ) :
    sigPow (1 : Matrix (Fin m) (Fin m) ℝ) (1 / 2) * (sigPow (1 : Matrix (Fin m) (Fin m) ℝ) (1 / 2))ᵀ
      = 1 := by
  obtain ⟨h1, h2⟩ := sigPow_half (Matrix.PosDef.one : (1 : Matrix (Fin m) (Fin m) ℝ).PosDef)
  rw [h2, h1]

/-- Corollary 3.19 (ii) (`cor:TWA`) for real `Q` (`β = 1`) and `l = 1`, for a general `T`
(§11.1), the comparison form. -/
theorem twaET_cmp (τ : ℝ) (C : ℕ → ℝ) (k : ℕ) (hτ : 0 < τ) (hcmp : HCmp1E τ k)
    (h : (Fin 1 → ℝ) → ℝ) (B : ℝ) (L : ℝ≥0) (hB : ∀ x, |h x| ≤ B) (hL : LipschitzWith L h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (M K : ℕ) (T : Matrix (Fin M) (Fin K) ℝ) (X : Ω → Matrix (Fin K) (Fin N) ℝ),
      IsModelT τ C M K N T X → RegularEdge τ N (specOf (T * Tᵀ)) k →
      |(∫ ω, h (qVecT T (X ω) k 1)) - (∫ ω, h (goeEdge N 1 ω))| ≤ ε := by
  obtain ⟨K₀, N₁, hK⟩ := edge_univT_lip τ C 1 hτ
  obtain ⟨N₂, hN₂⟩ := hcmp h B L hB hL (ε / 2) (half_pos hε)
  obtain ⟨N₃, hN₃⟩ := edgeRate_eventually K₀ B L 1 (half_pos hε)
  refine ⟨max N₁ (max N₂ N₃), fun N hN Ω _ _ M K T X hm hk => ?_⟩
  have h1 := hK N (le_of_max_le_left hN) M K T X k hm hk h B L hB hL
  have h2 := hN₂ N (le_of_max_le_left (le_of_max_le_right hN)) M (specOf (T * Tᵀ))
    (refClassE_of_isModelT hm hk)
  have h3 := hN₃ N (le_of_max_le_right (le_of_max_le_right hN))
  calc |(∫ ω, h (qVecT T (X ω) k 1)) - (∫ ω, h (goeEdge N 1 ω))|
      ≤ |(∫ ω, h (qVecT T (X ω) k 1)) - bRef N (specOf (T * Tᵀ)) k 1 h| +
        |(bRef N (specOf (T * Tᵀ)) k 1 h) - (∫ ω, h (goeEdge N 1 ω))| := abs_sub_le _ _ _
    _ ≤ ε := by push_cast at h1 h3; linarith

/-- Corollary 3.19 (ii) (`cor:TWA`) for real `Q` (`β = 1`) and `l = 1`, for a general `T`
(§11.1), the convergence form. -/
theorem twaET_conv (τ : ℝ) (C : ℕ → ℝ) (k : ℕ) (hτ : 0 < τ) (hcmp : HCmp1E τ k)
    (ν : ProbabilityMeasure (Fin 1 → ℝ)) (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν))
    (Ω : ℕ → Type) [∀ n, MeasureSpace (Ω n)] [∀ n, IsProbabilityMeasure (ℙ : Measure (Ω n))]
    (Ms Ks Ns : ℕ → ℕ) (T : ∀ n, Matrix (Fin (Ms n)) (Fin (Ks n)) ℝ)
    (X : ∀ n, Ω n → Matrix (Fin (Ks n)) (Fin (Ns n)) ℝ) (hN : Tendsto Ns atTop atTop)
    (hm : ∀ n, IsModelT τ C (Ms n) (Ks n) (Ns n) (T n) (X n))
    (hk : ∀ n, RegularEdge τ (Ns n) (specOf (T n * (T n)ᵀ)) k) :
    TendstoInDistribution (fun n ω => qVecT (T n) (X n ω) k 1) atTop id
      (fun n => (ℙ : Measure (Ω n))) (ν : Measure (Fin 1 → ℝ)) := by
  refine tendstoInDistribution_of_goeCmp ν htw Ns hN Ω _
    (fun n => measurable_qVecT_of_entries' (hm n).entries k 1) ?_
  intro f B L hB hL ε hε
  obtain ⟨N₀, hN₀⟩ := twaET_cmp τ C k hτ hcmp f B L hB hL ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hN.eventually (eventually_ge_atTop N₀))
  exact ⟨n₀, fun n hn => hN₀ (Ns n) (hn₀ n hn) (Ms n) (Ks n) (T n) (X n) (hm n) (hk n)⟩

/-- Corollary 3.19 (ii), `β = 1`, `l = 1`, for a general `T` at `T = (I_{n+1}; 0)` (`Σ = T Tᵀ`
singular, `M_n = 2(n + 1)`, `K_n = n + 1`, `N_n = 2(n + 1)`, edge `k = 1`): every non-external
hypothesis holds; `H_cmp^{1,e}` and `γ_N → ν` are hypotheses. -/
example (hcmp : HCmp1E (1 / 5) 1) (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution
      (fun n (ω : SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) =>
        qVecT (tPad (n + 1)) (radXn (n + 1) ω) 1 1)
      atTop id (fun n => (ℙ : Measure (SignSpace (Fin (n + 1) × Fin (2 * (n + 1))))))
      (ν : Measure (Fin 1 → ℝ)) := by
  have hN : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id
  exact twaET_conv (1 / 5) (fun _ => 1) 1 (by norm_num) hcmp ν htw
    (fun n => SignSpace (Fin (n + 1) × Fin (2 * (n + 1)))) (fun n => 2 * (n + 1))
    (fun n => n + 1) (fun n => 2 * (n + 1)) (fun n => tPad (n + 1)) (fun n => radXn (n + 1)) hN
    (fun n => isModelT_tPad n.succ_pos) (fun n => (mpT_hyps n.succ_pos).2.2.1)

/-- Corollary 3.19 (ii), `β = 1`, `l = 1`, for a general `T` at the lower edge `k = 2`, with
`T = I^{1/2}` (`M_n = K_n = 2(n + 1)`, `N_n = n + 1`, `φ = 2`, Gaussian entries, `τ = 1/20`):
every non-external hypothesis holds; `H_cmp^{1,e}` and `γ_N → ν` are hypotheses. -/
example (hcmp : HCmp1E (1 / 10 / 2) 2) (ν : ProbabilityMeasure (Fin 1 → ℝ))
    (htw : Tendsto (fun N => goeEdgeLaw N 1) atTop (𝓝 ν)) :
    TendstoInDistribution
      (fun n (ω : GaussSpace (2 * (n + 1)) (n + 1)) =>
        qVecT (sigPow (1 : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℝ) (1 / 2))
          (gaussX (2 * (n + 1)) (n + 1) ω) 2 1)
      atTop id (fun n => (ℙ : Measure (GaussSpace (2 * (n + 1)) (n + 1))))
      (ν : Measure (Fin 1 → ℝ)) := by
  refine twaET_conv (1 / 10 / 2) gaussMoment 2 (by norm_num) hcmp ν htw
    (fun n => GaussSpace (2 * (n + 1)) (n + 1)) (fun n => 2 * (n + 1)) (fun n => 2 * (n + 1))
    (fun n => n + 1) (fun n => sigPow 1 (1 / 2)) (fun n => gaussX (2 * (n + 1)) (n + 1))
    (tendsto_add_atTop_nat 1) (fun n => ?_) (fun n => ?_)
  · exact (isModelT_sqrt_iff Matrix.PosDef.one).mpr
      ((isModel_two (Nat.succ_pos n)).mono (by norm_num) (by norm_num))
  · rw [sigPow_one_mul_transpose, specOf_one_eq]
    exact regularEdge_two n.succ_pos (by norm_num) le_rfl

/-- The comparison form of Corollary 3.19 (ii), `β = 1`, `l = 1`, for a general `T` at the lower
edge `k = 2`, with `T = I^{1/2}` (`M_n = K_n = 2(n + 1)`, `N_n = n + 1`, Gaussian entries,
`τ = 1/20`), for the test function `x ↦ max (-1) (min (x 0) 1)`; `H_cmp^{1,e}` is a hypothesis. -/
example (hcmp : HCmp1E (1 / 10 / 2) 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      |(∫ ω : GaussSpace (2 * (n + 1)) (n + 1),
          max (-1) (min (qVecT (sigPow (1 : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) ℝ)
            (1 / 2)) (gaussX (2 * (n + 1)) (n + 1) ω) 2 1 0) 1)) -
        (∫ ω, max (-1) (min (goeEdge (n + 1) 1 ω 0) 1))| ≤ ε := by
  obtain ⟨N₀, hN₀⟩ := twaET_cmp (1 / 10 / 2) gaussMoment 2 (by norm_num) hcmp
    (fun x => max (-1) (min (x 0) 1)) 1 1 clampT_bdd clampT_lip ε hε
  refine ⟨N₀, fun n hn => hN₀ (n + 1) (by omega) (2 * (n + 1)) (2 * (n + 1)) (sigPow 1 (1 / 2))
    (gaussX (2 * (n + 1)) (n + 1))
    ((isModelT_sqrt_iff Matrix.PosDef.one).mpr
      ((isModel_two (Nat.succ_pos n)).mono (by norm_num) (by norm_num))) ?_⟩
  rw [sigPow_one_mul_transpose, specOf_one_eq]
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
#print axioms twaET_cmp
#print axioms twaET_conv

end Anisotropic
